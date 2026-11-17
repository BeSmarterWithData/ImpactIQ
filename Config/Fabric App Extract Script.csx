// Fabric App Extract Script
// Parses the saved, extracted frontend scripts of Fabric App backups and writes the query catalog that the
// PowerShell extract turns into worksheet rows. Tabular Editor 2 runs it against Blank Model.bim; the request
// file path arrives in the IMPACTIQ_FABRIC_APP_EXTRACT_REQUEST environment variable.
// Tabular Editor 2 compiles C# 5 and accepts type declarations only before the executable statements, so the
// code below is plain C# 5 classes followed by a single Run() call.

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;

// PowerShell's -eq, -in and -match are case-insensitive unless written -ceq, -cin or -cmatch. The parser logic was
// ported from PowerShell, so these helpers keep each comparison's case rule explicit.
static class FaPs
{
    public static bool Eq(string a, string b)
    {
        return string.Equals(a, b, StringComparison.OrdinalIgnoreCase);
    }

    public static bool In(string value, params string[] set)
    {
        for (int i = 0; i < set.Length; i++) { if (string.Equals(value, set[i], StringComparison.OrdinalIgnoreCase)) return true; }
        return false;
    }

    public static bool CIn(string value, params string[] set)
    {
        for (int i = 0; i < set.Length; i++) { if (string.Equals(value, set[i], StringComparison.Ordinal)) return true; }
        return false;
    }

    public static string[] Append(string[] items, string item)
    {
        string[] result = new string[items.Length + 1];
        Array.Copy(items, result, items.Length);
        result[items.Length] = item;
        return result;
    }

    public static List<string> SortedIgnoreCase(IEnumerable<string> values)
    {
        List<string> list = new List<string>(values);
        list.Sort(StringComparer.CurrentCultureIgnoreCase);
        return list;
    }

    public static string CollapseWhitespace(string text)
    {
        return Regex.Replace(text, @"\s+", " ", RegexOptions.CultureInvariant).Trim();
    }
}

class FaTok
{
    public string Kind;
    public string Value;
    public int Start;
    public int End;

    public FaTok(string kind, string value, int start, int end)
    {
        Kind = kind; Value = value; Start = start; End = end;
    }
}

class FaQuery
{
    public string Symbol;
    public string Evidence;
    public string Text;
    public List<string> Expressions = new List<string>();
    // Interpolations that only carry data (numbers, escaped text, value lists); they cannot declare or name DAX objects.
    public List<string> ValueExpressions = new List<string>();
    public int Start;
    public int End;
    public int Line;
    public int Column;
    public List<string> ConnectionAliases = new List<string>();
    public string UnexpandedSource = "";
}

// Behaviour switches. Improved resolves minified names by scope and recognises value-only helpers and JavaScript
// artifacts; strictParity (a request flag) restores the original PowerShell parser's behaviour for regression tests.
static class FaOptions
{
    public static bool Improved = true;
}

class FaBinding
{
    public string Kind;
    public string[] Parameters;
    public string Text;
    public Dictionary<string, string> Locals;
    public int Position;
    public int ScopeStart;
    public int ScopeEnd;
    public Dictionary<string, FaBinding> Home;
    // Other bindings of the same name in different scopes (minified bundles reuse short names).
    public FaBinding Next;
    // Source spans (start, end pairs) inside this binding's scope where another declaration of the name hides it.
    public List<int> Excluded;
    public int NameIndex;

    public FaBinding Copy()
    {
        return (FaBinding)MemberwiseClone();
    }
}

class FaDecl
{
    public string Name;
    public int Start;
    public int End;
    public int TokenIndex;
}

class FaFunctionScope
{
    public int Start;
    public int End;
    public List<string> Names = new List<string>();
}

class FaImport
{
    public string Local;
    public string Name;
    public string From;
}

class FaCatalog
{
    public List<FaQuery> Queries = new List<FaQuery>();
    public List<string> ScriptReferences = new List<string>();
    public Dictionary<string, string> Constants = new Dictionary<string, string>(StringComparer.Ordinal);
    public List<string> FieldCatalog = new List<string>();
    public List<FaImport> Imports = new List<FaImport>();
    public Dictionary<string, string> Exports = new Dictionary<string, string>(StringComparer.Ordinal);
    public Dictionary<string, FaBinding> Bindings = new Dictionary<string, FaBinding>(StringComparer.Ordinal);
    public List<string> ShadowedNames = new List<string>();
    public bool BindingsDeferred;
    public string DeferredSource;
}

class FaScopeEntry
{
    public bool Expand;
    public string Text;
}

class FaTemplateResult
{
    public string Text;
    public List<string> Expressions;
    public bool Failed;
}

// Expands `${...}` interpolations of a captured template whose names are bound to string/template constants or to
// functions that return templates. Interpolations that cannot be determined statically are left exactly as written.
class FaTemplateExpander
{
    static readonly Regex RegexLiteralPattern = new Regex(@"\G/(?:\\[^\r\n]|\[(?:\\[^\r\n]|[^\]\\\r\n])*\]|[^/\\\[\r\n])+/[a-z]*", RegexOptions.CultureInvariant);
    static readonly Regex IdentifierOnly = new Regex(@"^[A-Za-z_$][\w$]*$", RegexOptions.CultureInvariant);
    static readonly Regex IdentifierHead = new Regex(@"^[A-Za-z_$][\w$]*", RegexOptions.CultureInvariant);
    static readonly Regex CallPattern = new Regex(@"^(?<name>[A-Za-z_$][\w$]*)\s*\((?<arguments>[\s\S]*)\)$", RegexOptions.CultureInvariant);
    static readonly Regex LiteralArgument = new Regex(@"^(?<quote>[""'])(?<body>(?:\\[\s\S]|(?!\k<quote>)[^\\])*)\k<quote>$", RegexOptions.CultureInvariant);
    static readonly Regex IdentifierStart = new Regex(@"[A-Za-z_$]", RegexOptions.CultureInvariant | RegexOptions.IgnoreCase);
    static readonly Regex IdentifierPart = new Regex(@"[\w$.]", RegexOptions.CultureInvariant | RegexOptions.IgnoreCase);

    // Set when a `${...}` span cannot be delimited reliably; the caller then keeps the text and expressions it already had.
    bool failed;

    public static FaTemplateResult Expand(string text, int position, Dictionary<string, FaBinding> bindings)
    {
        FaTemplateExpander expander = new FaTemplateExpander();
        string expanded = expander.ExpandText(text, position, 0, new string[0], NewScope(), bindings);
        List<string> expressions = expander.GetExpressions(expanded);
        if (expander.failed) return new FaTemplateResult { Text = text, Expressions = null, Failed = true };
        return new FaTemplateResult { Text = expanded, Expressions = expressions, Failed = false };
    }

    static Dictionary<string, FaScopeEntry> NewScope()
    {
        return new Dictionary<string, FaScopeEntry>(StringComparer.OrdinalIgnoreCase);
    }

    // End index of the string, template or regular-expression literal that starts at index: -1 when it is
    // unterminated, -2 when no literal starts there. A lone quote inside a regex (`/"/g`) must not start a string.
    int SkipLiteral(string text, int index)
    {
        char c = text[index];
        if (c == '`') return SkipTemplate(text, index);
        if (c == '"' || c == '\'')
        {
            int end = index + 1;
            while (end < text.Length && text[end] != c) { if (text[end] == '\\') end++; end++; }
            if (end >= text.Length) return -1;
            return end;
        }
        if (c == '/' && index + 1 < text.Length && text[index + 1] != '/' && text[index + 1] != '*')
        {
            int before = index - 1;
            while (before >= 0 && char.IsWhiteSpace(text[before])) before--;
            if (before < 0 || "(,=:[!&|?{};+-*%<>~^".IndexOf(text[before]) >= 0)
            {
                Match match = RegexLiteralPattern.Match(text, index);
                if (match.Success) return index + match.Length - 1;
            }
        }
        return -2;
    }

    int SkipTemplate(string text, int start)
    {
        int cursor = start + 1;
        while (cursor < text.Length)
        {
            char c = text[cursor];
            if (c == '\\') { cursor += 2; continue; }
            if (c == '`') return cursor;
            if (c == '$' && cursor + 1 < text.Length && text[cursor + 1] == '{')
            {
                int close = FindExpressionEnd(text, cursor + 2);
                if (close < 0) return -1;
                cursor = close + 1;
                continue;
            }
            cursor++;
        }
        return -1;
    }

    // Index of the `}` that closes an interpolation whose body starts at start, or -1.
    int FindExpressionEnd(string text, int start)
    {
        int depth = 1;
        int cursor = start;
        while (cursor < text.Length)
        {
            char c = text[cursor];
            int end = SkipLiteral(text, cursor);
            if (end == -1) return -1;
            if (end >= 0) { cursor = end + 1; continue; }
            if (c == '{') depth++;
            else if (c == '}')
            {
                depth--;
                if (depth == 0) return cursor;
            }
            cursor++;
        }
        return -1;
    }

    // Index of the `)` matching the `(` at open, or -1.
    int FindCallEnd(string text, int open)
    {
        int depth = 0;
        int cursor = open;
        while (cursor < text.Length)
        {
            char c = text[cursor];
            int end = SkipLiteral(text, cursor);
            if (end == -1) return -1;
            if (end >= 0) { cursor = end + 1; continue; }
            if (c == '(') depth++;
            else if (c == ')')
            {
                depth--;
                if (depth == 0) return cursor;
            }
            cursor++;
        }
        return -1;
    }

    // Every `${...}` interpolation inside an expression's text, including nested ones.
    public static List<string> NestedInterpolations(string text)
    {
        FaTemplateExpander expander = new FaTemplateExpander();
        List<string> found = new List<string>();
        int cursor = 0;
        int open;
        while ((open = text.IndexOf("${", cursor, StringComparison.Ordinal)) >= 0)
        {
            int close = expander.FindExpressionEnd(text, open + 2);
            if (close < 0) break;
            found.Add(text.Substring(open + 2, close - open - 2));
            cursor = open + 2;
        }
        return found;
    }

    List<string> GetExpressions(string text)
    {
        List<string> expressions = new List<string>();
        int cursor = 0;
        int open;
        while ((open = text.IndexOf("${", cursor, StringComparison.Ordinal)) >= 0)
        {
            int close = FindExpressionEnd(text, open + 2);
            if (close < 0) { failed = true; break; }
            expressions.Add(text.Substring(open + 2, close - open - 2));
            cursor = close + 1;
        }
        return expressions;
    }

    // Top-level comma-separated arguments of a call body, or null when it is not one balanced argument list.
    List<string> SplitArguments(string text)
    {
        List<string> parts = new List<string>();
        int depth = 0;
        int start = 0;
        int cursor = 0;
        while (cursor < text.Length)
        {
            char c = text[cursor];
            int end = SkipLiteral(text, cursor);
            if (end == -1) return null;
            if (end >= 0) { cursor = end + 1; continue; }
            if (c == '(' || c == '[' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '}')
            {
                depth--;
                if (depth < 0) return null;
            }
            else if (c == ',' && depth == 0)
            {
                parts.Add(text.Substring(start, cursor - start));
                start = cursor + 1;
            }
            cursor++;
        }
        if (depth != 0) return null;
        if (text.Trim().Length > 0) parts.Add(text.Substring(start));
        return parts;
    }

    static bool IsVisible(FaBinding binding, int position)
    {
        if (binding.ScopeEnd >= 0 && (position < binding.ScopeStart || position > binding.ScopeEnd)) return false;
        if (binding.Excluded != null)
        {
            for (int i = 0; i + 1 < binding.Excluded.Count; i += 2)
            {
                if (position >= binding.Excluded[i] && position <= binding.Excluded[i + 1]) return false;
            }
        }
        return true;
    }

    // The innermost binding of the name that is visible at position, when it has the requested kind.
    public static FaBinding FindBinding(Dictionary<string, FaBinding> table, string name, string kind, int position)
    {
        return GetBinding(table, name, kind, position);
    }

    static FaBinding GetBinding(Dictionary<string, FaBinding> table, string name, string kind, int position)
    {
        FaBinding head;
        if (!table.TryGetValue(name, out head)) return null;
        FaBinding best = null;
        for (FaBinding candidate = head; candidate != null; candidate = candidate.Next)
        {
            if (!IsVisible(candidate, position)) continue;
            if (best == null || (candidate.ScopeEnd < 0 ? -1 : candidate.ScopeStart) > (best.ScopeEnd < 0 ? -1 : best.ScopeStart)) best = candidate;
        }
        if (best != null && string.Equals(best.Kind, kind, StringComparison.Ordinal)) return best;
        return null;
    }

    // scope maps names visible inside the function being expanded to their text: arguments (used as given) and
    // local constants (expanded in the same scope). table is the binding table the text belongs to.
    string ExpandText(string text, int position, int depth, string[] active, Dictionary<string, FaScopeEntry> scope, Dictionary<string, FaBinding> table)
    {
        StringBuilder builder = new StringBuilder();
        int cursor = 0;
        while (cursor < text.Length)
        {
            int open = text.IndexOf("${", cursor, StringComparison.Ordinal);
            if (open < 0) { builder.Append(text.Substring(cursor)); break; }
            builder.Append(text.Substring(cursor, open - cursor));
            int close = FindExpressionEnd(text, open + 2);
            if (close < 0) { failed = true; builder.Append(text.Substring(open)); break; }
            string replacement = ResolveExpression(text.Substring(open + 2, close - open - 2), position, depth, active, scope, table, false);
            builder.Append(replacement != null ? replacement : text.Substring(open, close - open + 1));
            cursor = close + 1;
        }
        return builder.ToString();
    }

    // Replaces calls to inlinable helpers inside a larger expression (a conditional branch, for example) with the
    // helper's text as a template literal, so the dependency stage sees it like any other template branch.
    string ExpandCalls(string expression, int position, int depth, string[] active, Dictionary<string, FaScopeEntry> scope, Dictionary<string, FaBinding> table)
    {
        StringBuilder builder = new StringBuilder();
        bool changed = false;
        int cursor = 0;
        while (cursor < expression.Length)
        {
            char c = expression[cursor];
            int literalEnd = SkipLiteral(expression, cursor);
            if (literalEnd == -1) { builder.Append(expression.Substring(cursor)); break; }
            if (literalEnd >= 0)
            {
                builder.Append(expression.Substring(cursor, literalEnd - cursor + 1));
                cursor = literalEnd + 1;
                continue;
            }
            if (IdentifierStart.IsMatch(c.ToString()) && (cursor == 0 || !IdentifierPart.IsMatch(expression[cursor - 1].ToString())))
            {
                string identifier = IdentifierHead.Match(expression.Substring(cursor)).Value;
                int afterIdentifier = cursor + identifier.Length;
                int parenthesis = afterIdentifier;
                while (parenthesis < expression.Length && char.IsWhiteSpace(expression[parenthesis])) parenthesis++;
                if (parenthesis < expression.Length && expression[parenthesis] == '(' && GetBinding(table, identifier, "Function", position) != null)
                {
                    int close = FindCallEnd(expression, parenthesis);
                    if (close >= 0)
                    {
                        string resolved = ResolveExpression(expression.Substring(cursor, close - cursor + 1), position, depth, active, scope, table, true);
                        if (resolved != null)
                        {
                            builder.Append("`" + resolved.Replace("\\", "\\\\").Replace("`", "\\`") + "`");
                            changed = true;
                            cursor = close + 1;
                            continue;
                        }
                    }
                }
                builder.Append(identifier);
                cursor = afterIdentifier;
                continue;
            }
            builder.Append(c);
            cursor++;
        }
        return changed ? builder.ToString() : null;
    }

    // The text an interpolation contributes, or null when it cannot be determined statically.
    string ResolveExpression(string expression, int position, int depth, string[] active, Dictionary<string, FaScopeEntry> scope, Dictionary<string, FaBinding> table, bool noEmbedded)
    {
        if (depth >= 4) return null;
        string trimmed = expression.Trim();
        if (IdentifierOnly.IsMatch(trimmed))
        {
            FaScopeEntry entry;
            if (scope != null && scope.TryGetValue(trimmed, out entry))
            {
                if (!entry.Expand) return entry.Text;
                if (Array.IndexOf(active, "local:" + trimmed) >= 0) return null;
                return ExpandText(entry.Text, position, depth + 1, FaPs.Append(active, "local:" + trimmed), scope, table);
            }
            FaBinding constant = GetBinding(table, trimmed, "Constant", position);
            if (constant == null || Array.IndexOf(active, trimmed) >= 0 || !IsVisible(constant, position)) return null;
            Dictionary<string, FaBinding> constantHome = constant.Home != null ? constant.Home : table;
            return ExpandText(constant.Text, constant.Position, depth + 1, FaPs.Append(active, trimmed), NewScope(), constantHome);
        }
        Match call = CallPattern.Match(trimmed);
        if (call.Success)
        {
            string name = call.Groups["name"].Value;
            FaBinding function = GetBinding(table, name, "Function", position);
            List<string> arguments = function != null ? SplitArguments(call.Groups["arguments"].Value) : null;
            if (function != null && arguments != null)
            {
                if (Array.IndexOf(active, name) >= 0 || !IsVisible(function, position) || arguments.Count > function.Parameters.Length) return null;
                Dictionary<string, FaScopeEntry> functionScope = NewScope();
                for (int i = 0; i < arguments.Count; i++)
                {
                    string slot = i < function.Parameters.Length ? function.Parameters[i] : null;
                    if (string.IsNullOrEmpty(slot)) continue;
                    string argumentText = arguments[i].Trim();
                    // A plain quoted literal is substituted as its text; anything else stays a runtime expression of the caller.
                    Match literal = LiteralArgument.Match(argumentText);
                    string literalText = null;
                    if (literal.Success)
                    {
                        try { literalText = Regex.Unescape(literal.Groups["body"].Value); }
                        catch (Exception) { literalText = literal.Groups["body"].Value; }
                    }
                    FaScopeEntry slotEntry = new FaScopeEntry();
                    slotEntry.Expand = false;
                    slotEntry.Text = literal.Success ? literalText : "${" + argumentText + "}";
                    functionScope[slot] = slotEntry;
                }
                if (function.Locals != null)
                {
                    foreach (string localName in function.Locals.Keys)
                    {
                        if (!functionScope.ContainsKey(localName))
                        {
                            FaScopeEntry localEntry = new FaScopeEntry();
                            localEntry.Expand = true;
                            localEntry.Text = function.Locals[localName];
                            functionScope[localName] = localEntry;
                        }
                    }
                }
                Dictionary<string, FaBinding> functionHome = function.Home != null ? function.Home : table;
                return ExpandText(function.Text, function.Position, depth + 1, FaPs.Append(active, name), functionScope, functionHome);
            }
        }
        if (noEmbedded) return null;
        string modified = ExpandCalls(trimmed, position, depth + 1, active, scope, table);
        if (modified != null) return "${" + modified + "}";
        return null;
    }
}

class FaRange
{
    public string Name;
    public int Start;
    public int End;
    public int OpenIndex;
    public int CloseIndex;
    public int ParameterOpen;
    public string[] Parameters;
}

class FaArg
{
    public int Start;
    public int End;
}

class FaInlineParameters
{
    public string[] Parameters;
    public int Close;
}

class FaDeclFrame
{
    public int Paren;
    public int Bracket;
    public int Brace;
    public string Keyword;
}

class FaSpecifier
{
    public string Name;
    public string Alias;
}

class FaSpecifiers
{
    public List<FaSpecifier> Items;
    public int Close;
}

class FaRouteParameter
{
    public string Name;
    public FaArg Default;
}

class FaRouteNode
{
    public string Key;
    public int Start;
    public int End;
    public string Scope;
    public string Kind;
    public List<string> Values = new List<string>();
    public HashSet<string> ValueSet = new HashSet<string>(StringComparer.Ordinal);
    public Dictionary<string, bool> Dependents = new Dictionary<string, bool>(StringComparer.Ordinal);
}

class FaRouteValue
{
    public FaRouteNode Node;
    public string Value;
}

class FaRouteCall
{
    public string Caller;
    public string Callee;
    public FaArg[] Arguments;
}

class FaRouteSymbol<T>
{
    public string Scope;
    public T Value;
}

class FaModelRoute
{
    public int ParameterIndex;
    public int QueryStart;
    public int QueryEnd;
    public int QueryParameterIndex;
    public FaRange Range;
}

class FaSourceCall
{
    public int Index;
    public string Alias;
}

// Ordered set of strings: the PowerShell code relied on HashSet enumeration following insertion order.
class FaOrderedSet
{
    List<string> items = new List<string>();
    HashSet<string> seen = new HashSet<string>(StringComparer.Ordinal);

    public bool Add(string value)
    {
        if (!seen.Add(value)) return false;
        items.Add(value);
        return true;
    }

    public int Count { get { return items.Count; } }
    public List<string> Items { get { return items; } }
}

// Port of Get-FabricAppDaxSource. Token kinds, offsets and every heuristic follow the PowerShell parser so the
// resulting query catalog is the same; comments mark the places where PowerShell semantics needed care.
class FaParser
{
    static readonly Regex Lex = new Regex(@"\G(?:(?<space>\s+)|(?<comment>//[^\r\n]*|/\*[\s\S]*?\*/)|(?<string>""(?:\\[\s\S]|[^""\\\r\n])*""|'(?:\\[\s\S]|[^'\\\r\n])*')|(?<word>[a-zA-Z_$][\w$]*)|(?<number>\d+(?:\.\d+)?)|(?<punct>=>|\+\+|--|&&|\|\||\?\?|[^\s]))", RegexOptions.Compiled | RegexOptions.CultureInvariant);
    static readonly int GroupSpace = Lex.GroupNumberFromName("space");
    static readonly int GroupComment = Lex.GroupNumberFromName("comment");
    static readonly int GroupString = Lex.GroupNumberFromName("string");
    static readonly int GroupWord = Lex.GroupNumberFromName("word");
    static readonly Regex RegexLiteral = new Regex(@"\G/(?:\\[^\r\n]|\[(?:\\[^\r\n]|[^\]\\\r\n])*\]|[^/\\\[\r\n])+/[a-z]*", RegexOptions.Compiled | RegexOptions.CultureInvariant);
    static readonly Regex TemplateChunk = new Regex(@"\G(?:[^`\\$]+|\\(?:\r\n|[\s\S])|\$(?!\{))+", RegexOptions.Compiled | RegexOptions.CultureInvariant);
    static readonly Regex EscapePattern = new Regex(@"\\(?:\r\n|[\s\S])", RegexOptions.Compiled | RegexOptions.CultureInvariant);
    const string QueryStartPattern = @"^(?:\s+|(?://|--)[^\r\n]*(?:\r?\n|$)|/\*[\s\S]*?\*/)*";
    static readonly Regex QueryHead = new Regex(QueryStartPattern + @"(?:EVALUATE|DEFINE)\b", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex QueryHeadWithVar = new Regex(QueryStartPattern + @"(?:EVALUATE|DEFINE|VAR)\b", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex ConfigFragment = new Regex(@"^\[[A-Za-z_][^\]\r\n]*\]$", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex ConfigArtifact = new Regex(@"^\[(?:object [A-Z]\w*|[^\]]*[""'=\\<>][^\]]*|(?:[A-Za-z0-9]-[A-Za-z0-9])+)\]$", RegexOptions.CultureInvariant);
    // Further JavaScript runtime artifacts: inspected-object markers and lowercase kebab/dotted identifiers.
    static readonly Regex ConfigArtifactExtra = new Regex(@"^\[(?:object [A-Za-z]\w*|null|undefined|NaN|Infinity|Circular|Object|Array|Function|Symbol|Getter|Setter|Getter/Setter|[a-z0-9]+(?:[-.][a-z0-9]+)+)\]$", RegexOptions.CultureInvariant);
    static readonly Regex QuotedTableColumn = new Regex(@"'[^'\r\n]+'\[[^\]\r\n]+\]", RegexOptions.CultureInvariant);
    static readonly Regex TableOrMeasure = new Regex(@"'[^'\r\n]+'\s*\[[^\]\r\n]+\]|(?<![\w'\]])\[[A-Za-z_][^\]\r\n]*\]", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex DaxFunctionOrKeyword = new Regex(@"(?<![\w.])[A-Z][A-Z0-9.]{2,}\s*\(|\b(?:EVALUATE|DEFINE|VAR)\b", RegexOptions.CultureInvariant);
    static readonly Regex OwnerPattern = new Regex(@"(?:function\s+(?<name>[\w$]+)\([^{}]*\)\s*\{\s*return\s*|(?:const|let|var)\s+(?<name>[\w$]+)\s*=\s*)$", RegexOptions.CultureInvariant);
    static readonly Regex ScriptReference = new Regex(@"^(?:\.{0,2}/|https://)[^\s]+\.m?js(?:\?[^\s]*)?$", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex GuidPattern = new Regex(@"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$", RegexOptions.CultureInvariant);
    static readonly Regex HexRun = new Regex(@"^[0-9a-fA-F]+$", RegexOptions.CultureInvariant);
    static readonly Regex HexBraced = new Regex(@"^[0-9a-fA-F]{1,6}$", RegexOptions.CultureInvariant);
    static readonly Regex IdentifierValue = new Regex(@"^[a-zA-Z_$][\w$]*$", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex ConnectionWords = new Regex(@"\b(?:connection|semanticModel|semanticModels|dax|query)\b", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex WrapperCall = new Regex(@"(?<![\w$])[a-zA-Z_$][\w$]*\s*\(\s*[""'](?<route>[a-zA-Z_$][\w$]*)[""']\s*,", RegexOptions.CultureInvariant);
    static readonly HashSet<string> RegexPrecursors = new HashSet<string>(new string[] { "(", "[", "{", ",", ":", ";", "=", "=>", "!", "?", "&&", "||", "??", "+", "-", "*", "/", "%", "&", "|", "^", "~", "<", ">", "return", "throw", "case", "typeof", "void", "delete", "yield" }, StringComparer.OrdinalIgnoreCase);

    string src;
    bool requireBindings;
    List<FaTok> tokens = new List<FaTok>();
    List<FaQuery> queries = new List<FaQuery>();
    List<string> references = new List<string>();
    HashSet<string> referenceSet = new HashSet<string>(StringComparer.Ordinal);
    int pos;
    int depth;
    int queryCount;
    int fragmentCount;
    int mappingCount;
    List<FaQuery> ordered;
    Dictionary<int, int> literalTokenByStart = new Dictionary<int, int>();
    Dictionary<int, FaQuery[]> queriesByToken = new Dictionary<int, FaQuery[]>();
    int tokenCount;
    Dictionary<int, int> tokenCloseByOpen = new Dictionary<int, int>();
    Dictionary<int, int> punctCloseByOpen = new Dictionary<int, int>();
    Dictionary<string, List<int>> callSitesByName = new Dictionary<string, List<int>>(StringComparer.OrdinalIgnoreCase);
    List<int> legacyRouteSites = new List<int>();
    int[] nextRoundOpen;
    int[] nextBraceOpen;
    int[] valueEndByStart;
    Dictionary<int, FaArg[]> argumentRangesByOpen = new Dictionary<int, FaArg[]>();
    Dictionary<string, string> aliasVariables = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
    List<FaRange> functionRanges = new List<FaRange>();

    public static FaCatalog Parse(string source, bool requireBindings)
    {
        FaParser parser = new FaParser();
        parser.src = source;
        parser.requireBindings = requireBindings;
        return parser.Run();
    }

    // Token accessors mirror PowerShell: an index outside the list yields $null, which equals nothing.
    string V(int i)
    {
        return i >= 0 && i < tokens.Count ? tokens[i].Value : null;
    }

    string K(int i)
    {
        return i >= 0 && i < tokens.Count ? tokens[i].Kind : null;
    }

    bool Is(int i, string expected)
    {
        string v = V(i);
        return v != null && string.Equals(v, expected, StringComparison.OrdinalIgnoreCase);
    }

    bool CIs(int i, string expected)
    {
        string v = V(i);
        return v != null && string.Equals(v, expected, StringComparison.Ordinal);
    }

    bool In(int i, params string[] set)
    {
        string v = V(i);
        return v != null && FaPs.In(v, set);
    }

    bool CIn(int i, params string[] set)
    {
        string v = V(i);
        return v != null && FaPs.CIn(v, set);
    }

    static string DecodeJs(string text)
    {
        if (text.IndexOf('\\') < 0) return text;
        StringBuilder builder = new StringBuilder();
        int offset = 0;
        foreach (Match escape in EscapePattern.Matches(text))
        {
            if (escape.Index < offset) continue;
            builder.Append(text, offset, escape.Index - offset);
            string code = escape.Value.Substring(1);
            offset = escape.Index + escape.Length;
            if (string.Equals(code, "n", StringComparison.Ordinal)) builder.Append('\n');
            else if (string.Equals(code, "r", StringComparison.Ordinal)) builder.Append('\r');
            else if (string.Equals(code, "t", StringComparison.Ordinal)) builder.Append('\t');
            else if (string.Equals(code, "b", StringComparison.Ordinal)) builder.Append((char)8);
            else if (string.Equals(code, "f", StringComparison.Ordinal)) builder.Append((char)12);
            else if (string.Equals(code, "v", StringComparison.Ordinal)) builder.Append((char)11);
            else if (string.Equals(code, "0", StringComparison.Ordinal))
            {
                if (offset < text.Length && char.IsDigit(text[offset])) throw new Exception("Legacy octal escapes are unsupported.");
                builder.Append('\0');
            }
            else if (code == "\n" || code == "\r" || code == "\r\n") { }
            else if (FaPs.In(code, "x", "u"))
            {
                int width = FaPs.Eq(code, "x") ? 2 : 4;
                if (FaPs.Eq(code, "u") && offset < text.Length && text[offset] == '{')
                {
                    int end = text.IndexOf('}', offset);
                    if (end < 0) throw new Exception("Invalid Unicode escape.");
                    string hex = text.Substring(offset + 1, end - offset - 1);
                    if (!HexBraced.IsMatch(hex)) throw new Exception("Invalid Unicode escape.");
                    int value = Convert.ToInt32(hex, 16);
                    if (value <= 65535) builder.Append((char)value);
                    else builder.Append(char.ConvertFromUtf32(value));
                    offset = end + 1;
                }
                else
                {
                    if (offset + width > text.Length) throw new Exception("Incomplete hexadecimal escape.");
                    string hex = text.Substring(offset, width);
                    if (!HexRun.IsMatch(hex)) throw new Exception("Invalid hexadecimal escape.");
                    builder.Append((char)Convert.ToInt32(hex, 16));
                    offset += width;
                }
            }
            else if (code.Length == 1 && code[0] >= '1' && code[0] <= '9') throw new Exception("Legacy numeric escapes are unsupported.");
            else builder.Append(code);
        }
        builder.Append(text, offset, text.Length - offset);
        return builder.ToString();
    }

    void AddLiteral(int start, int end, string text, List<string> expressions)
    {
        bool isQuery = QueryHead.IsMatch(text);
        if (!isQuery && expressions.Count > 0 && text.TrimStart().StartsWith("${", StringComparison.Ordinal))
        {
            // Builders often begin with a shared DEFINE header interpolation (`${header} EVALUATE ...`).
            string remaining = text.TrimStart();
            foreach (string expression in expressions)
            {
                string marker = "${" + expression + "}";
                if (!remaining.StartsWith(marker, StringComparison.Ordinal)) break;
                remaining = remaining.Substring(marker.Length).TrimStart();
                if (!remaining.StartsWith("${", StringComparison.Ordinal)) break;
            }
            isQuery = QueryHeadWithVar.IsMatch(remaining);
        }
        string fragmentEvidence = "";
        if (!isQuery && text.Length > 2 && text.IndexOf('[') >= 0)
        {
            if (expressions.Count == 0 && ConfigFragment.IsMatch(text))
            {
                // JavaScript artifacts ("[object Array]"), HTML/CSS attribute selectors and regex classes are not measure names.
                if (!ConfigArtifact.IsMatch(text) && !(FaOptions.Improved && ConfigArtifactExtra.IsMatch(text))) fragmentEvidence = "ConfigExpression";
            }
            else if (text.Length > 20 && (QuotedTableColumn.IsMatch(text) || (TableOrMeasure.IsMatch(text) && DaxFunctionOrKeyword.IsMatch(text))))
            {
                fragmentEvidence = "DaxFragment";
            }
        }
        if (isQuery || fragmentEvidence.Length > 0)
        {
            int prefixStart = Math.Max(0, start - 300);
            string prefix = src.Substring(prefixStart, start - prefixStart);
            Match owner = OwnerPattern.Match(prefix);
            string symbol;
            if (owner.Success) symbol = owner.Groups["name"].Value;
            else if (isQuery) { queryCount++; symbol = "query_" + queryCount; }
            else { fragmentCount++; symbol = "fragment_" + fragmentCount; }
            if (owner.Success && isQuery) queryCount++;
            FaQuery query = new FaQuery();
            query.Symbol = symbol;
            query.Evidence = fragmentEvidence.Length > 0 ? fragmentEvidence : (expressions.Count > 0 ? "DynamicTemplate" : "StaticCandidate");
            query.Text = text.Trim();
            query.Expressions = new List<string>(expressions);
            query.Start = start;
            query.End = end;
            queries.Add(query);
        }
        if (expressions.Count == 0 && ScriptReference.IsMatch(text) && referenceSet.Add(text)) references.Add(text);
    }

    void ReadCode(bool untilBrace)
    {
        depth++;
        if (depth > 128) throw new Exception("JavaScript nesting limit exceeded.");
        int braceDepth = 0;
        bool regexAllowed = true;
        try
        {
            while (pos < src.Length)
            {
                int start = pos;
                Match match = Lex.Match(src, start);
                if (!match.Success) throw new Exception("Could not scan JavaScript token.");
                string value = match.Value;
                pos += match.Length;
                if (match.Groups[GroupSpace].Success || match.Groups[GroupComment].Success) continue;
                if (value == "}" && untilBrace && braceDepth == 0) return;
                if (value == "{") braceDepth++;
                if (value == "}") braceDepth--;
                if (match.Groups[GroupString].Success)
                {
                    string text = DecodeJs(value.Substring(1, value.Length - 2));
                    tokens.Add(new FaTok("string", text, start, pos));
                    AddLiteral(start, pos, text, new List<string>());
                    regexAllowed = false;
                    continue;
                }
                if (value == "\"" || value == "'") throw new Exception("Unterminated JavaScript string.");
                if (value == "`")
                {
                    StringBuilder builder = new StringBuilder();
                    List<string> expressions = new List<string>();
                    bool closed = false;
                    while (pos < src.Length)
                    {
                        Match chunk = TemplateChunk.Match(src, pos);
                        if (chunk.Success)
                        {
                            string normalized = chunk.Value.Replace("\r\n", "\n").Replace("\r", "\n");
                            builder.Append(DecodeJs(normalized));
                            pos += chunk.Length;
                        }
                        else if (src[pos] == '`') { pos++; closed = true; break; }
                        else if (pos + 1 < src.Length && src[pos] == '$' && src[pos + 1] == '{')
                        {
                            pos += 2;
                            int expressionStart = pos;
                            ReadCode(true);
                            string expression = src.Substring(expressionStart, pos - expressionStart - 1);
                            expressions.Add(expression);
                            builder.Append("${" + expression + "}");
                        }
                        else throw new Exception("Unsupported JavaScript template.");
                    }
                    if (!closed) throw new Exception("Unterminated JavaScript template.");
                    string templateText = builder.ToString();
                    tokens.Add(new FaTok("template", templateText, start, pos));
                    AddLiteral(start, pos, templateText, expressions);
                    regexAllowed = false;
                    continue;
                }
                if (value == "/" && regexAllowed)
                {
                    Match literal = RegexLiteral.Match(src, start);
                    if (!literal.Success) throw new Exception("Unterminated or unsupported JavaScript regular expression.");
                    pos = start + literal.Length;
                    tokens.Add(new FaTok("regex", "", start, pos));
                    regexAllowed = false;
                    continue;
                }
                tokens.Add(new FaTok(match.Groups[GroupWord].Success ? "word" : "punct", value, start, pos));
                regexAllowed = RegexPrecursors.Contains(value);
            }
            if (untilBrace) throw new Exception("Unterminated JavaScript template expression.");
        }
        finally { depth--; }
    }

    Dictionary<string, object> ReadObject(ref int index, int objectDepth)
    {
        if (objectDepth > 8 || index >= tokens.Count || !Is(index, "{")) throw new Exception("Unsupported model configuration.");
        index++;
        Dictionary<string, object> result = new Dictionary<string, object>(StringComparer.Ordinal);
        while (index < tokens.Count && !Is(index, "}"))
        {
            FaTok key = tokens[index];
            if ((key.Kind != "word" && key.Kind != "string") || result.ContainsKey(key.Value)) throw new Exception("Nonliteral or duplicate configuration property.");
            index++;
            if (index >= tokens.Count || !Is(index, ":")) throw new Exception("Unsupported configuration property.");
            index++;
            if (index >= tokens.Count) throw new Exception("Incomplete configuration.");
            if (tokens[index].Kind == "string") { result[key.Value] = tokens[index].Value; index++; }
            else if (Is(index, "{")) result[key.Value] = ReadObject(ref index, objectDepth + 1);
            else throw new Exception("Nonliteral model configuration.");
            if (index < tokens.Count && Is(index, ",")) index++;
            else if (index >= tokens.Count || !Is(index, "}")) throw new Exception("Unsupported configuration expression.");
        }
        if (index >= tokens.Count) throw new Exception("Unterminated configuration object.");
        index++;
        return result;
    }

    // Scans the whole token list for the `semanticModels` configuration. Only the number of valid mappings matters
    // here (it disables the config-only shortcut); the app's connector file supplies the real model mappings.
    void ReadMappings()
    {
        for (int tokenIndex = 0; tokenIndex < tokens.Count - 2; tokenIndex++)
        {
            if (!Is(tokenIndex, "semanticModels") || !Is(tokenIndex + 1, ":")) continue;
            if (!Is(tokenIndex + 2, "{")) continue;
            int objectIndex = tokenIndex + 2;
            try
            {
                Dictionary<string, object> configuration = ReadObject(ref objectIndex, 0);
                foreach (string alias in configuration.Keys)
                {
                    Dictionary<string, object> model = configuration[alias] as Dictionary<string, object>;
                    if (model == null) continue;
                    // A missing key raises in PowerShell for a generic dictionary, abandoning the rest of this object.
                    if (!model.ContainsKey("workspaceId")) throw new KeyNotFoundException();
                    string workspaceId = model["workspaceId"] as string;
                    if (workspaceId == null || !GuidPattern.IsMatch(workspaceId)) continue;
                    if (!model.ContainsKey("itemId")) throw new KeyNotFoundException();
                    string itemId = model["itemId"] as string;
                    if (itemId == null || !GuidPattern.IsMatch(itemId)) continue;
                    mappingCount++;
                }
            }
            catch (Exception) { }
        }
    }

    void BuildTokenIndexes()
    {
        ordered = new List<FaQuery>(queries.OrderBy(q => q.Start));
        for (int tokenIndex = 0; tokenIndex < tokens.Count; tokenIndex++)
        {
            FaTok token = tokens[tokenIndex];
            if (token.Kind != "string" && token.Kind != "template") continue;
            if (tokenIndex >= 2 && !literalTokenByStart.ContainsKey(token.Start)) literalTokenByStart[token.Start] = tokenIndex;
            // Template tokens can contain other query literals and are emitted after their children.
            int low = 0;
            int high = ordered.Count;
            while (low < high)
            {
                int middle = low + ((high - low) >> 1);
                if (ordered[middle].Start < token.Start) low = middle + 1;
                else high = middle;
            }
            List<FaQuery> contained = null;
            for (int queryIndex = low; queryIndex < ordered.Count; queryIndex++)
            {
                FaQuery query = ordered[queryIndex];
                if (query.Start >= token.End) break;
                if (query.End <= token.End)
                {
                    if (contained == null) contained = new List<FaQuery>();
                    contained.Add(query);
                }
            }
            if (contained != null) queriesByToken[tokenIndex] = contained.ToArray();
        }
        int line = 1;
        int lineStart = 0;
        int scanOffset = 0;
        foreach (FaQuery query in ordered)
        {
            while (scanOffset < query.Start)
            {
                int newline = src.IndexOf('\n', scanOffset);
                if (newline < 0 || newline >= query.Start) break;
                line++;
                lineStart = newline + 1;
                scanOffset = lineStart;
            }
            query.Line = line;
            query.Column = query.Start - lineStart + 1;
        }
    }

    void BuildDelimiterIndexes()
    {
        tokenCount = tokens.Count;
        Dictionary<string, Stack<int>> delimiterStacks = new Dictionary<string, Stack<int>>();
        Dictionary<string, Stack<int>> punctStacks = new Dictionary<string, Stack<int>>();
        foreach (string opening in new string[] { "(", "[", "{" })
        {
            delimiterStacks[opening] = new Stack<int>();
            punctStacks[opening] = new Stack<int>();
        }
        Dictionary<string, string> openingByClose = new Dictionary<string, string>();
        openingByClose[")"] = "(";
        openingByClose["]"] = "[";
        openingByClose["}"] = "{";
        for (int index = 0; index < tokenCount; index++)
        {
            FaTok token = tokens[index];
            string value = token.Value;
            if (FaPs.In(value, "connection", "model", "semanticModel")) legacyRouteSites.Add(index);
            if (delimiterStacks.ContainsKey(value))
            {
                delimiterStacks[value].Push(index);
                if (token.Kind == "punct") punctStacks[value].Push(index);
            }
            else if (openingByClose.ContainsKey(value))
            {
                string opening = openingByClose[value];
                if (delimiterStacks[opening].Count > 0) tokenCloseByOpen[delimiterStacks[opening].Pop()] = index;
                if (token.Kind == "punct" && punctStacks[opening].Count > 0) punctCloseByOpen[punctStacks[opening].Pop()] = index;
            }
            if (value.Length > 0 && index + 1 < tokenCount && Is(index + 1, "("))
            {
                List<int> sites;
                if (!callSitesByName.TryGetValue(value, out sites)) { sites = new List<int>(); callSitesByName[value] = sites; }
                sites.Add(index);
            }
        }
        nextRoundOpen = new int[tokenCount + 1];
        nextBraceOpen = new int[tokenCount + 1];
        valueEndByStart = new int[tokenCount + 1];
        nextRoundOpen[tokenCount] = nextBraceOpen[tokenCount] = valueEndByStart[tokenCount] = tokenCount;
        for (int index = tokenCount - 1; index >= 0; index--)
        {
            FaTok token = tokens[index];
            nextRoundOpen[index] = Is(index, "(") ? index : nextRoundOpen[index + 1];
            nextBraceOpen[index] = Is(index, "{") ? index : nextBraceOpen[index + 1];
            if (token.Kind == "punct" && FaPs.In(token.Value, ",", ";", ")", "]", "}")) valueEndByStart[index] = index;
            else if (token.Kind == "punct" && FaPs.In(token.Value, "(", "[", "{"))
            {
                int close;
                valueEndByStart[index] = punctCloseByOpen.TryGetValue(index, out close) ? valueEndByStart[close + 1] : tokenCount;
            }
            else valueEndByStart[index] = valueEndByStart[index + 1];
        }
    }

    List<int> CallSites(string name)
    {
        List<int> sites;
        return callSitesByName.TryGetValue(name, out sites) ? sites : new List<int>();
    }

    FaArg[] ArgumentRanges(int opening)
    {
        FaArg[] cached;
        if (argumentRangesByOpen.TryGetValue(opening, out cached)) return cached;
        List<FaArg> arguments = new List<FaArg>();
        int argumentStart = opening + 1;
        int round = 0, square = 0, curly = 0;
        for (int cursor = argumentStart; cursor < tokenCount; cursor++)
        {
            string value = tokens[cursor].Value;
            if (Is(cursor, "(")) round++;
            else if (Is(cursor, ")"))
            {
                if (round == 0 && square == 0 && curly == 0)
                {
                    arguments.Add(new FaArg { Start = argumentStart, End = cursor });
                    break;
                }
                round--;
            }
            else if (Is(cursor, "[")) square++;
            else if (Is(cursor, "]")) square--;
            else if (Is(cursor, "{")) curly++;
            else if (Is(cursor, "}")) curly--;
            else if (Is(cursor, ",") && round == 0 && square == 0 && curly == 0)
            {
                arguments.Add(new FaArg { Start = argumentStart, End = cursor });
                argumentStart = cursor + 1;
            }
        }
        FaArg[] result = arguments.ToArray();
        argumentRangesByOpen[opening] = result;
        return result;
    }

    void BuildAliasVariablesAndFunctions()
    {
        for (int tokenIndex = 0; tokenIndex < tokens.Count - 2; tokenIndex++)
        {
            if (K(tokenIndex) != "word" || !Is(tokenIndex + 1, "=") || K(tokenIndex + 2) != "string" || !IdentifierValue.IsMatch(V(tokenIndex + 2))) continue;
            aliasVariables[tokens[tokenIndex].Value] = tokens[tokenIndex + 2].Value;
        }
        for (int tokenIndex = 0; tokenIndex < tokens.Count - 4; tokenIndex++)
        {
            if (!Is(tokenIndex, "function") || K(tokenIndex + 1) != "word") continue;
            int openParenthesis = nextRoundOpen[tokenIndex + 2];
            if (openParenthesis >= tokens.Count) continue;
            int closeParenthesis;
            if (!tokenCloseByOpen.TryGetValue(openParenthesis, out closeParenthesis)) continue;
            int openBrace = nextBraceOpen[closeParenthesis + 1];
            if (openBrace >= tokens.Count) continue;
            int closeBrace;
            if (!tokenCloseByOpen.TryGetValue(openBrace, out closeBrace)) continue;
            List<string> parameters = new List<string>();
            for (int index = openParenthesis + 1; index < closeParenthesis; index++)
            {
                if (tokens[index].Kind == "word") parameters.Add(tokens[index].Value);
            }
            FaRange range = new FaRange();
            range.Name = tokens[tokenIndex + 1].Value;
            range.Start = tokens[tokenIndex].Start;
            range.End = tokens[closeBrace].End;
            range.OpenIndex = openBrace;
            range.CloseIndex = closeBrace;
            range.ParameterOpen = openParenthesis;
            range.Parameters = parameters.ToArray();
            functionRanges.Add(range);
        }
        for (int tokenIndex = 0; tokenIndex < tokens.Count - 6; tokenIndex++)
        {
            if (K(tokenIndex) != "word" || !Is(tokenIndex + 1, "=")) continue;
            int parameterOpen = tokenIndex + 2;
            if (!Is(parameterOpen, "(")) continue;
            int parameterClose;
            if (!tokenCloseByOpen.TryGetValue(parameterOpen, out parameterClose)) parameterClose = -1;
            if (parameterClose < 0 || parameterClose + 2 >= tokens.Count || !Is(parameterClose + 1, "=>")) continue;
            int bodyOpen = parameterClose + 2;
            if (!(Is(bodyOpen, "(") || Is(bodyOpen, "{") || Is(bodyOpen, "["))) continue;
            int bodyClose;
            if (!tokenCloseByOpen.TryGetValue(bodyOpen, out bodyClose)) continue;
            List<string> parameters = new List<string>();
            for (int index = parameterOpen + 1; index < parameterClose; index++)
            {
                if (tokens[index].Kind == "word") parameters.Add(tokens[index].Value);
            }
            FaRange range = new FaRange();
            range.Name = tokens[tokenIndex].Value;
            range.Start = tokens[tokenIndex].Start;
            range.End = tokens[bodyClose].End;
            range.OpenIndex = bodyOpen;
            range.CloseIndex = bodyClose;
            range.ParameterOpen = parameterOpen;
            range.Parameters = parameters.ToArray();
            functionRanges.Add(range);
        }
    }

    static readonly Regex ConstantTable = new Regex(@"^'[^'\r\n]+'$", RegexOptions.CultureInvariant);
    static readonly Regex FieldName = new Regex(@"^[^\[\]'""\r\n]{1,100}$", RegexOptions.CultureInvariant);
    static readonly Regex InterpolatedName = new Regex(@"\$\{\s*([A-Za-z_$][\w$]*)\s*[(}]", RegexOptions.CultureInvariant);
    static readonly Regex CalledName = new Regex(@"(?<![\w$.])([A-Za-z_$][\w$]*)\s*\(", RegexOptions.CultureInvariant);
    static readonly Regex ExpressionHead = new Regex(@"^\s*([A-Za-z_$][\w$]*)", RegexOptions.CultureInvariant);
    static readonly Regex UpperName = new Regex(@"^[A-Z][A-Z0-9_.]*$", RegexOptions.CultureInvariant);
    static readonly Regex BodyPiece = new Regex(@"(?<![\w.])[A-Z][A-Z0-9.]{2,}\s*\(|(?<![\w'\]])\[[A-Za-z_][^\]]*\]", RegexOptions.CultureInvariant);
    static readonly HashSet<string> IgnoredNames = new HashSet<string>(new string[] { "if", "for", "while", "switch", "catch", "function", "return", "typeof", "new", "await", "void", "String", "Number", "Boolean", "Math", "Object", "JSON", "Array", "Date", "parseInt", "parseFloat", "isNaN", "isFinite", "encodeURIComponent", "BigInt", "Set", "Map", "WeakMap", "WeakSet", "Error", "RegExp", "Symbol", "Promise", "Intl" }, StringComparer.Ordinal);

    Dictionary<string, string> tableConstants = new Dictionary<string, string>(StringComparer.Ordinal);
    SortedSet<string> fieldCatalog = new SortedSet<string>(StringComparer.Ordinal);
    HashSet<string> parameterNames = new HashSet<string>(StringComparer.Ordinal);
    Dictionary<string, int> inlineBindingCounts = new Dictionary<string, int>(StringComparer.Ordinal);
    Dictionary<int, int> inlineEnclosingOpen = new Dictionary<int, int>();
    List<int> inlineSites = new List<int>();
    HashSet<int> inlineDeclarators = new HashSet<int>();
    HashSet<string> inlineNeeded = new HashSet<string>(StringComparer.Ordinal);
    List<FaImport> moduleImports = new List<FaImport>();
    Dictionary<string, string> moduleExports = new Dictionary<string, string>(StringComparer.Ordinal);
    Dictionary<int, string> declarationKeyword = new Dictionary<int, string>();
    Dictionary<string, FaBinding> inlineBindings = new Dictionary<string, FaBinding>(StringComparer.Ordinal);

    FaCatalog Run()
    {
        ReadCode(false);
        ReadMappings();
        BuildTokenIndexes();
        bool configOnly = !requireBindings && mappingCount == 0 && !ordered.Any(q => !string.Equals(q.Evidence, "ConfigExpression", StringComparison.Ordinal)) && !ConnectionWords.IsMatch(src);
        BuildDelimiterIndexes();
        BuildAliasVariablesAndFunctions();
        if (configOnly) return ConfigOnlyCatalog();
        if (FaOptions.Improved) BuildAliasEntries();
        BuildConstants();
        DiscoverInlineBindings();
        ExpandInlineQueries();
        if (FaOptions.Improved) ClassifyValueExpressions();
        BuildDiagnostics();
        BuildScopes();
        BuildOwners();
        AddWrapperRoutes();
        AddConnectionRoutes();
        ApplyAliasHeuristics();
        FaCatalog catalog = new FaCatalog();
        catalog.Queries = ordered;
        catalog.ScriptReferences = references;
        catalog.Constants = tableConstants;
        catalog.FieldCatalog = new List<string>(fieldCatalog);
        catalog.Imports = moduleImports;
        catalog.Exports = moduleExports;
        catalog.Bindings = inlineBindings;
        catalog.ShadowedNames = new List<string>(inlineBindingCounts.Keys);
        catalog.ShadowedNames.AddRange(parameterNames);
        return catalog;
    }

    // Standalone configuration strings need no call graph; imported providers can request the full catalog later.
    FaCatalog ConfigOnlyCatalog()
    {
        Dictionary<string, List<string>> routesByOwner = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        foreach (FaQuery query in ordered)
        {
            FaOrderedSet aliases = new FaOrderedSet();
            int prefixStart = Math.Max(0, query.Start - 500);
            string prefix = src.Substring(prefixStart, query.Start - prefixStart);
            MatchCollection wrapperMatches = WrapperCall.Matches(prefix);
            if (wrapperMatches.Count > 0) aliases.Add(wrapperMatches[wrapperMatches.Count - 1].Groups["route"].Value);
            FaRange ownerRange = null;
            foreach (FaRange range in functionRanges)
            {
                if (range.Start <= query.Start && range.End >= query.Start && (ownerRange == null || range.End - range.Start < ownerRange.End - ownerRange.Start)) ownerRange = range;
            }
            string owner = ownerRange != null ? ownerRange.Name : query.Symbol;
            int literalIndex;
            if (ownerRange == null && literalTokenByStart.TryGetValue(query.Start, out literalIndex))
            {
                if (Is(literalIndex - 1, "=") && K(literalIndex - 2) == "word") owner = tokens[literalIndex - 2].Value;
            }
            if (owner.Length > 0 && !owner.StartsWith("query_", StringComparison.OrdinalIgnoreCase))
            {
                List<string> routes;
                if (!routesByOwner.TryGetValue(owner, out routes))
                {
                    routes = new List<string>();
                    string ownerPattern = @"(?<![\w$])" + Regex.Escape(owner) + @"(?![\w$])\s*\(\s*[""'](?<route>[a-zA-Z_$][\w$]*)[""']\s*,";
                    foreach (Match call in Regex.Matches(src, ownerPattern)) routes.Add(call.Groups["route"].Value);
                    routesByOwner[owner] = routes;
                }
                foreach (string route in routes) aliases.Add(route);
            }
            query.ConnectionAliases = FaPs.SortedIgnoreCase(aliases.Items);
            query.UnexpandedSource = "";
        }
        FaCatalog catalog = new FaCatalog();
        catalog.Queries = ordered;
        catalog.ScriptReferences = references;
        catalog.BindingsDeferred = true;
        catalog.DeferredSource = src;
        return catalog;
    }

    // Resolve `${name}` table interpolations only for names bound exactly once to a quoted table identifier.
    void BuildConstants()
    {
        Dictionary<string, int> assignmentCounts = new Dictionary<string, int>(StringComparer.Ordinal);
        Dictionary<string, string> constantCandidates = new Dictionary<string, string>(StringComparer.Ordinal);
        List<string> candidateOrder = new List<string>();
        for (int tokenIndex = 0; tokenIndex < tokens.Count - 2; tokenIndex++)
        {
            if (K(tokenIndex) != "word" || !Is(tokenIndex + 1, "=")) continue;
            string name = tokens[tokenIndex].Value;
            int count;
            assignmentCounts[name] = 1 + (assignmentCounts.TryGetValue(name, out count) ? count : 0);
            if (K(tokenIndex + 2) == "string" && ConstantTable.IsMatch(tokens[tokenIndex + 2].Value))
            {
                if (!constantCandidates.ContainsKey(name)) candidateOrder.Add(name);
                constantCandidates[name] = tokens[tokenIndex + 2].Value;
            }
        }
        foreach (FaRange range in functionRanges)
        {
            foreach (string parameter in range.Parameters) parameterNames.Add(parameter);
        }
        foreach (string name in candidateOrder)
        {
            if (assignmentCounts[name] == 1 && !parameterNames.Contains(name)) tableConstants[name] = constantCandidates[name];
        }
        // Field names declared in static `{ field: "Name" }` catalogs; used only to expand runtime-selected columns.
        for (int tokenIndex = 0; tokenIndex < tokens.Count - 2; tokenIndex++)
        {
            if ((K(tokenIndex) == "word" || K(tokenIndex) == "string") && CIs(tokenIndex, "field") &&
                Is(tokenIndex + 1, ":") && K(tokenIndex + 2) == "string" && FieldName.IsMatch(tokens[tokenIndex + 2].Value))
            {
                fieldCatalog.Add(tokens[tokenIndex + 2].Value);
            }
        }
    }

    FaSpecifiers ReadInlineSpecifiers(int open)
    {
        List<FaSpecifier> items = new List<FaSpecifier>();
        int cursor = open + 1;
        while (cursor < tokens.Count && !Is(cursor, "}"))
        {
            FaTok current = tokens[cursor];
            if (Is(cursor, ",")) { cursor++; continue; }
            if (current.Kind != "word" && current.Kind != "string") return null;
            string alias = current.Value;
            if (cursor + 2 < tokens.Count && K(cursor + 1) == "word" && CIs(cursor + 1, "as"))
            {
                alias = tokens[cursor + 2].Value;
                cursor += 2;
            }
            items.Add(new FaSpecifier { Name = current.Value, Alias = alias });
            cursor++;
        }
        if (cursor >= tokens.Count) return null;
        return new FaSpecifiers { Items = items, Close = cursor };
    }

    bool TestInlineLiteralEnd(int index)
    {
        if (index >= tokens.Count) return true;
        FaTok next = tokens[index];
        return FaPs.In(next.Value, ",", ";", "}", ")") ||
            ((next.Kind == "word" || next.Kind == "string" || next.Kind == "template") && !FaPs.CIn(next.Value, "in", "of", "instanceof"));
    }

    // Parameter slots of a function whose `(` is token open. A slot is the parameter name, or '' for a destructuring
    // pattern or rest parameter (its names are then simply left as runtime expressions); defaults are skipped.
    FaInlineParameters GetInlineParameters(int open)
    {
        List<string> slots = new List<string>();
        int level = 0;
        int cursor = open + 1;
        bool atStart = true;
        while (cursor < tokens.Count)
        {
            FaTok current = tokens[cursor];
            if (current.Kind == "punct")
            {
                if (FaPs.In(current.Value, "(", "[", "{")) level++;
                else if (FaPs.In(current.Value, ")", "]", "}"))
                {
                    if (level == 0)
                    {
                        if (!Is(cursor, ")")) return null;
                        return new FaInlineParameters { Parameters = slots.ToArray(), Close = cursor };
                    }
                    level--;
                }
                else if (Is(cursor, ",") && level == 0) { atStart = true; cursor++; continue; }
            }
            if (atStart)
            {
                atStart = false;
                string nextValue = cursor + 1 < tokens.Count ? tokens[cursor + 1].Value : "";
                slots.Add(current.Kind == "word" && FaPs.In(nextValue, ",", ")", "=") ? current.Value : "");
            }
            cursor++;
        }
        return null;
    }

    // A template's interpolation tokens are emitted before the template token, so find the literal by where it
    // starts in the source (the first non-space character after the preceding token) instead of by token offset.
    int FindInlineLiteral(int previousIndex)
    {
        int expectedStart = tokens[previousIndex].End;
        while (expectedStart < src.Length && char.IsWhiteSpace(src[expectedStart])) expectedStart++;
        if (expectedStart >= src.Length || (src[expectedStart] != '"' && src[expectedStart] != '\'' && src[expectedStart] != '`')) return -1;
        int index;
        if (literalTokenByStart.TryGetValue(expectedStart, out index))
        {
            if (index > previousIndex && index <= previousIndex + 4000) return index;
        }
        return -1;
    }

    // Index of the literal token returned by a function body or arrow body that starts at token start.
    int GetInlineArrowLiteral(int start)
    {
        if (start >= tokens.Count) return -1;
        int direct = FindInlineLiteral(start - 1);
        if (direct >= 0)
        {
            if (TestInlineLiteralEnd(direct + 1)) return direct;
            return -1;
        }
        if (Is(start, "("))
        {
            int literalIndex = FindInlineLiteral(start);
            if (literalIndex >= 0 && literalIndex + 1 < tokens.Count && Is(literalIndex + 1, ")")) return literalIndex;
            return -1;
        }
        if (Is(start, "{") && start + 1 < tokens.Count && CIs(start + 1, "return"))
        {
            int literalIndex = FindInlineLiteral(start + 1);
            if (literalIndex >= 0)
            {
                int after = literalIndex + 1;
                if (after < tokens.Count && Is(after, ";")) after++;
                if (after < tokens.Count && Is(after, "}")) return literalIndex;
            }
        }
        return -1;
    }

    // Visibility is stored as source positions (the declaring block's span), so expansion needs no token access.
    void SetInlineBinding(int nameIndex, string kind, string[] parameters, string text, Dictionary<string, string> locals, int bodyPosition)
    {
        int open = inlineEnclosingOpen[nameIndex];
        int scopeStart = 0;
        int scopeEnd = -1;
        if (open >= 0)
        {
            int close;
            if (!punctCloseByOpen.TryGetValue(open, out close)) return;
            scopeStart = tokens[open].Start;
            scopeEnd = tokens[close].End;
        }
        FaBinding binding = new FaBinding();
        binding.Kind = kind;
        binding.Parameters = parameters;
        binding.Text = text;
        binding.Locals = locals;
        binding.Position = bodyPosition >= 0 ? bodyPosition : tokens[nameIndex].Start;
        binding.ScopeStart = scopeStart;
        binding.ScopeEnd = scopeEnd;
        binding.Home = null;
        binding.NameIndex = nameIndex;
        string bindingName = tokens[nameIndex].Value;
        FaBinding existing;
        if (FaOptions.Improved && inlineBindings.TryGetValue(bindingName, out existing))
        {
            while (existing.Next != null) existing = existing.Next;
            existing.Next = binding;
        }
        else inlineBindings[bindingName] = binding;
    }

    void RegisterInlineBinding(int nameIndex, string[] parameters, int literalIndex)
    {
        SetInlineBinding(nameIndex, parameters == null ? "Constant" : "Function", parameters, tokens[literalIndex].Value, null, -1);
    }

    // A function with logic before its return (guards, local constants, conditional returns): its DAX contribution is
    // every template returned at its top level, plus quoted strings that read as DAX, which includes both branches of a
    // conditional. Local constants declared in the body are kept so `${local}` inside the returned text can be expanded.
    FaBinding GetInlineBodyBinding(int open, int close)
    {
        List<FaTok> candidates = new List<FaTok>();
        int paren = 0;
        for (int index = open + 1; index < close; index++)
        {
            FaTok current = tokens[index];
            if (current.Kind == "punct")
            {
                if (FaPs.In(current.Value, "(", "[")) paren++;
                else if (FaPs.In(current.Value, ")", "]")) paren--;
                continue;
            }
            if (current.Kind != "word" || !string.Equals(current.Value, "return", StringComparison.Ordinal) || paren != 0) continue;
            int level = 0;
            int end = index + 1;
            while (end < close)
            {
                FaTok scan = tokens[end];
                if (scan.Kind == "punct")
                {
                    if (FaPs.In(scan.Value, "(", "[", "{")) level++;
                    else if (FaPs.In(scan.Value, ")", "]", "}")) { if (level == 0) break; level--; }
                    else if (Is(end, ";") && level == 0) break;
                }
                else if ((scan.Kind == "string" || scan.Kind == "template") && level == 0) candidates.Add(scan);
                end++;
            }
            index = end - 1;
        }
        // Interpolation tokens precede their template, so a literal inside another literal's span is not top level.
        List<string> pieces = new List<string>();
        FaTok last = null;
        foreach (FaTok candidate in candidates.OrderBy(c => c.Start))
        {
            if (last != null && candidate.Start >= last.Start && candidate.End <= last.End) continue;
            last = candidate;
            if (candidate.Kind == "template" || BodyPiece.IsMatch(candidate.Value)) pieces.Add(candidate.Value);
        }
        if (pieces.Count == 0) return null;
        Dictionary<string, string> locals = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
        HashSet<string> ambiguous = new HashSet<string>(StringComparer.Ordinal);
        int braces = 0;
        int parentheses = 0;
        for (int index = open + 1; index < close - 1; index++)
        {
            FaTok current = tokens[index];
            if (current.Kind == "punct")
            {
                if (Is(index, "{")) braces++;
                else if (Is(index, "}")) braces--;
                else if (FaPs.In(current.Value, "(", "[")) parentheses++;
                else if (FaPs.In(current.Value, ")", "]")) parentheses--;
                continue;
            }
            if (current.Kind != "word" || braces != 0 || parentheses != 0 || !Is(index + 1, "=")) continue;
            if (!CIn(index - 1, "const", "let", "var") && !Is(index - 1, ",")) continue;
            int literalIndex = FindInlineLiteral(index + 1);
            if (literalIndex < 0 || !TestInlineLiteralEnd(literalIndex + 1)) continue;
            if (locals.ContainsKey(current.Value)) ambiguous.Add(current.Value);
            else locals[current.Value] = tokens[literalIndex].Value;
        }
        foreach (string name in ambiguous) locals.Remove(name);
        FaBinding body = new FaBinding();
        body.Text = string.Join(" ", pieces.ToArray());
        body.Locals = locals;
        return body;
    }

    void RegisterInlineFunction(int nameIndex, string[] parameters, int bodyStart)
    {
        // Names inside a function's text are resolved from inside its body, so its own locals and parameters shadow outer names.
        int bodyPosition = FaOptions.Improved ? tokens[bodyStart].Start : -1;
        int literalIndex = GetInlineArrowLiteral(bodyStart);
        if (literalIndex >= 0)
        {
            SetInlineBinding(nameIndex, "Function", parameters, tokens[literalIndex].Value, null, bodyPosition);
            return;
        }
        int close;
        if (!Is(bodyStart, "{") || !punctCloseByOpen.TryGetValue(bodyStart, out close)) return;
        FaBinding body = GetInlineBodyBinding(bodyStart, close);
        if (body == null) return;
        SetInlineBinding(nameIndex, "Function", parameters, body.Text, body.Locals, bodyPosition);
    }

    // Inline template interpolations that name a string/template constant or a function that only returns a template,
    // so the dependency stage sees the DAX they contribute. A name qualifies only when it is bound exactly once in the
    // bundle, is never a parameter, and the usage sits inside the block that declares it; anything else stays opaque.
    void DiscoverInlineBindings()
    {
        // Only names used as `${name}` or `${name(...)}` can be inlined, which keeps the token pass cheap on large bundles.
        // ES module imports and exports let a template in one script file use constants and helpers defined in another.
        for (int tokenIndex = 0; tokenIndex < tokens.Count; tokenIndex++)
        {
            FaTok token = tokens[tokenIndex];
            if (token.Kind == "template")
            {
                if (token.Value.IndexOf("${", StringComparison.Ordinal) < 0) continue;
                foreach (Match usage in InterpolatedName.Matches(token.Value)) inlineNeeded.Add(usage.Groups[1].Value);
                // Calls inside larger expressions are registered too, so the diagnostics can say whether the helper is inlinable.
                foreach (Match usage in CalledName.Matches(token.Value)) inlineNeeded.Add(usage.Groups[1].Value);
            }
            else if (token.Kind == "word" && (CIs(tokenIndex, "import") || CIs(tokenIndex, "export")) && tokenIndex + 2 < tokens.Count)
            {
                if (Is(tokenIndex + 1, "{"))
                {
                    FaSpecifiers specifiers = ReadInlineSpecifiers(tokenIndex + 1);
                    if (specifiers == null) continue;
                    if (CIs(tokenIndex, "export"))
                    {
                        foreach (FaSpecifier item in specifiers.Items) { moduleExports[item.Alias] = item.Name; inlineNeeded.Add(item.Name); }
                    }
                    else if (specifiers.Close + 2 < tokens.Count && CIs(specifiers.Close + 1, "from") && K(specifiers.Close + 2) == "string")
                    {
                        foreach (FaSpecifier item in specifiers.Items) moduleImports.Add(new FaImport { Local = item.Alias, Name = item.Name, From = tokens[specifiers.Close + 2].Value });
                    }
                }
                else if (CIs(tokenIndex, "export") && CIn(tokenIndex + 1, "const", "let", "var", "function", "class") && K(tokenIndex + 2) == "word")
                {
                    moduleExports[tokens[tokenIndex + 2].Value] = tokens[tokenIndex + 2].Value;
                    inlineNeeded.Add(tokens[tokenIndex + 2].Value);
                }
            }
        }
        if (FaOptions.Improved)
        {
            // `const yBe=ej`: the target of an alias must be tracked too.
            for (int pass = 0; pass < 3; pass++)
            {
                bool added = false;
                for (int i = 1; i < tokens.Count - 3; i++)
                {
                    if (tokens[i].Kind == "word" && inlineNeeded.Contains(tokens[i].Value) && Is(i + 1, "=") && K(i + 2) == "word" &&
                        In(i + 3, ",", ";", "}") && (CIn(i - 1, "const", "let", "var") || Is(i - 1, ",")) && inlineNeeded.Add(tokens[i + 2].Value)) added = true;
                }
                if (!added) break;
            }
        }
        if (inlineNeeded.Count > 0)
        {
            int inlineTokenCount = tokens.Count;
            Stack<int> inlineBlockStack = new Stack<int>();
            // Minified code declares most names in comma-separated lists (`const a=1,b="x",c=t=>...`), so a `,name=` at
            // the level of an open const/let/var statement is a declaration too.
            Stack<FaDeclFrame> declarationStack = new Stack<FaDeclFrame>();
            int parenDepth = 0, bracketDepth = 0, braceDepth = 0;
            for (int tokenIndex = 0; tokenIndex < inlineTokenCount; tokenIndex++)
            {
                FaTok token = tokens[tokenIndex];
                if (token.Kind == "punct")
                {
                    string tokenValue = token.Value;
                    if (tokenValue == "{") { inlineBlockStack.Push(tokenIndex); braceDepth++; }
                    else if (tokenValue == "}")
                    {
                        if (inlineBlockStack.Count > 0) inlineBlockStack.Pop();
                        braceDepth--;
                        while (declarationStack.Count > 0 && declarationStack.Peek().Brace > braceDepth) declarationStack.Pop();
                    }
                    else if (tokenValue == "(") parenDepth++;
                    else if (tokenValue == ")")
                    {
                        parenDepth--;
                        while (declarationStack.Count > 0 && declarationStack.Peek().Paren > parenDepth) declarationStack.Pop();
                    }
                    else if (tokenValue == "[") bracketDepth++;
                    else if (tokenValue == "]")
                    {
                        bracketDepth--;
                        while (declarationStack.Count > 0 && declarationStack.Peek().Bracket > bracketDepth) declarationStack.Pop();
                    }
                    else if (tokenValue == ";" && declarationStack.Count > 0)
                    {
                        FaDeclFrame top = declarationStack.Peek();
                        if (top.Paren == parenDepth && top.Bracket == bracketDepth && top.Brace == braceDepth) declarationStack.Pop();
                    }
                }
                else if (token.Kind == "word")
                {
                    string tokenText = token.Value;
                    bool isDeclarator = false;
                    string declaratorKeyword = null;
                    if (tokenText == "const" || tokenText == "let" || tokenText == "var")
                    {
                        declarationStack.Push(new FaDeclFrame { Paren = parenDepth, Bracket = bracketDepth, Brace = braceDepth, Keyword = tokenText });
                    }
                    else if (declarationStack.Count > 0 && tokenIndex > 0 && tokenIndex + 1 < inlineTokenCount &&
                        Is(tokenIndex - 1, ",") && Is(tokenIndex + 1, "="))
                    {
                        FaDeclFrame top = declarationStack.Peek();
                        if (top.Paren == parenDepth && top.Bracket == bracketDepth && top.Brace == braceDepth)
                        {
                            isDeclarator = true;
                            declaratorKeyword = top.Keyword;
                            inlineDeclarators.Add(tokenIndex);
                        }
                    }
                    if (tokenIndex > 0 && inlineNeeded.Contains(tokenText))
                    {
                        if (isDeclarator || CIn(tokenIndex - 1, "const", "let", "var", "function", "class") ||
                            (tokenIndex >= 2 && Is(tokenIndex - 1, "(") && CIs(tokenIndex - 2, "catch")) ||
                            (tokenIndex + 1 < inlineTokenCount && Is(tokenIndex + 1, "=>")))
                        {
                            int count;
                            inlineBindingCounts[tokenText] = 1 + (inlineBindingCounts.TryGetValue(tokenText, out count) ? count : 0);
                            inlineEnclosingOpen[tokenIndex] = inlineBlockStack.Count > 0 ? inlineBlockStack.Peek() : -1;
                            inlineSites.Add(tokenIndex);
                            if (isDeclarator) declarationKeyword[tokenIndex] = declaratorKeyword;
                            else if (CIn(tokenIndex - 1, "const", "let", "var", "function", "class")) declarationKeyword[tokenIndex] = tokens[tokenIndex - 1].Value;
                        }
                    }
                }
            }
        }
        foreach (int tokenIndex in inlineSites)
        {
            FaTok token = tokens[tokenIndex];
            if (tokenIndex >= tokens.Count - 3) continue;
            if (!FaOptions.Improved && (inlineBindingCounts[token.Value] != 1 || parameterNames.Contains(token.Value))) continue;
            if (CIs(tokenIndex - 1, "function") && Is(tokenIndex + 1, "("))
            {
                FaInlineParameters parsed = GetInlineParameters(tokenIndex + 1);
                if (parsed != null && parsed.Close + 1 < tokens.Count && Is(parsed.Close + 1, "{"))
                {
                    RegisterInlineFunction(tokenIndex, parsed.Parameters, parsed.Close + 1);
                }
            }
            else if ((CIn(tokenIndex - 1, "const", "let", "var") || inlineDeclarators.Contains(tokenIndex)) && Is(tokenIndex + 1, "="))
            {
                int valueIndex = tokenIndex + 2;
                int literalIndex = FindInlineLiteral(tokenIndex + 1);
                if (literalIndex >= 0)
                {
                    if (TestInlineLiteralEnd(literalIndex + 1)) RegisterInlineBinding(tokenIndex, null, literalIndex);
                }
                else if (Is(valueIndex, "("))
                {
                    FaInlineParameters parsed = GetInlineParameters(valueIndex);
                    if (parsed != null && parsed.Close + 2 < tokens.Count && Is(parsed.Close + 1, "=>"))
                    {
                        RegisterInlineFunction(tokenIndex, parsed.Parameters, parsed.Close + 2);
                    }
                }
                else if (K(valueIndex) == "word" && valueIndex + 2 < tokens.Count && Is(valueIndex + 1, "=>"))
                {
                    RegisterInlineFunction(tokenIndex, new string[] { tokens[valueIndex].Value }, valueIndex + 2);
                }
                else if (FaOptions.Improved && K(valueIndex) == "word" && In(valueIndex + 1, ",", ";", "}"))
                {
                    aliasSites.Add(tokenIndex);
                }
            }
        }
        if (FaOptions.Improved)
        {
            ResolveBindingAliases();
            CollectExclusions();
        }
    }

    List<int> aliasSites = new List<int>();
    Dictionary<string, List<FaDecl>> declarationsByName = new Dictionary<string, List<FaDecl>>(StringComparer.Ordinal);

    // `const yBe=ej` makes yBe another name for a binding that is already registered.
    void ResolveBindingAliases()
    {
        for (int pass = 0; pass < 2; pass++)
        {
            foreach (int aliasIndex in aliasSites)
            {
                string aliasName = tokens[aliasIndex].Value;
                FaBinding existingAlias;
                bool registered = false;
                if (inlineBindings.TryGetValue(aliasName, out existingAlias))
                {
                    for (FaBinding scan = existingAlias; scan != null; scan = scan.Next) { if (scan.NameIndex == aliasIndex) registered = true; }
                }
                if (registered) continue;
                int open = inlineEnclosingOpen[aliasIndex];
                int close = -1;
                if (open >= 0 && !punctCloseByOpen.TryGetValue(open, out close)) continue;
                FaBinding source = null;
                int sourceIndex = aliasIndex + 2;
                FaBinding head;
                if (inlineBindings.TryGetValue(tokens[sourceIndex].Value, out head))
                {
                    int probe = tokens[aliasIndex].Start;
                    foreach (string kind in new string[] { "Function", "Constant" })
                    {
                        source = FaTemplateExpander.FindBinding(inlineBindings, tokens[sourceIndex].Value, kind, probe);
                        if (source != null) break;
                    }
                }
                if (source == null) continue;
                FaBinding binding = source.Copy();
                binding.Next = null;
                binding.Excluded = null;
                binding.NameIndex = aliasIndex;
                binding.ScopeStart = open >= 0 ? tokens[open].Start : 0;
                binding.ScopeEnd = open >= 0 ? tokens[close].End : -1;
                FaBinding tail;
                if (inlineBindings.TryGetValue(aliasName, out tail))
                {
                    while (tail.Next != null) tail = tail.Next;
                    tail.Next = binding;
                }
                else inlineBindings[aliasName] = binding;
            }
        }
    }

    // Every place a name is declared: variables and functions (block or function scoped) and function parameters.
    void CollectExclusions()
    {
        List<FaFunctionScope> functionScopes = CollectFunctionScopes(inlineNeeded);
        Dictionary<string, List<FaDecl>> declarations = new Dictionary<string, List<FaDecl>>(StringComparer.Ordinal);
        foreach (int site in inlineSites)
        {
            string keyword;
            if (!declarationKeyword.TryGetValue(site, out keyword)) continue;
            string name = tokens[site].Value;
            int start = 0;
            int end = int.MaxValue;
            if (keyword == "var" || keyword == "function")
            {
                int smallest = int.MaxValue;
                foreach (FaFunctionScope scope in functionScopes)
                {
                    int tokenStart = tokens[site].Start;
                    if (scope.Start <= tokenStart && tokenStart <= scope.End && scope.End - scope.Start < smallest)
                    {
                        smallest = scope.End - scope.Start;
                        start = scope.Start;
                        end = scope.End;
                    }
                }
            }
            else
            {
                int open = inlineEnclosingOpen[site];
                int close;
                if (open >= 0 && punctCloseByOpen.TryGetValue(open, out close)) { start = tokens[open].Start; end = tokens[close].End; }
            }
            AddDeclaration(declarations, name, start, end, site);
        }
        foreach (FaFunctionScope scope in functionScopes)
        {
            foreach (string name in scope.Names) AddDeclaration(declarations, name, scope.Start, scope.End, -1);
        }
        declarationsByName = declarations;
        foreach (KeyValuePair<string, FaBinding> pair in inlineBindings)
        {
            List<FaDecl> others;
            if (!declarations.TryGetValue(pair.Key, out others)) continue;
            for (FaBinding binding = pair.Value; binding != null; binding = binding.Next)
            {
                foreach (FaDecl other in others)
                {
                    if (other.TokenIndex == binding.NameIndex) continue;
                    if (binding.ScopeEnd >= 0 && (other.Start < binding.ScopeStart || other.End > binding.ScopeEnd)) continue;
                    if (binding.Excluded == null) binding.Excluded = new List<int>();
                    binding.Excluded.Add(other.Start);
                    binding.Excluded.Add(other.End);
                }
            }
        }
    }

    static void AddDeclaration(Dictionary<string, List<FaDecl>> declarations, string name, int start, int end, int tokenIndex)
    {
        List<FaDecl> list;
        if (!declarations.TryGetValue(name, out list)) { list = new List<FaDecl>(); declarations[name] = list; }
        list.Add(new FaDecl { Name = name, Start = start, End = end, TokenIndex = tokenIndex });
    }

    // End token index of an arrow function's expression body that starts at token start.
    int ExpressionBodyEnd(int start)
    {
        int level = 0;
        int cursor = start;
        while (cursor < tokens.Count)
        {
            string value = tokens[cursor].Kind == "punct" ? tokens[cursor].Value : null;
            if (value != null)
            {
                if (value == "(" || value == "[" || value == "{") level++;
                else if (value == ")" || value == "]" || value == "}")
                {
                    if (level == 0) break;
                    level--;
                }
                else if ((value == "," || value == ";") && level == 0) break;
            }
            cursor++;
        }
        return cursor - 1;
    }

    // Spans of every function-like construct with the names it binds (all words of its parameter list, which also
    // covers destructuring patterns): function declarations, arrow functions, methods and catch clauses.
    List<FaFunctionScope> CollectFunctionScopes(HashSet<string> keepNames)
    {
        List<FaFunctionScope> scopes = new List<FaFunctionScope>();
        Dictionary<int, int> openByClose = new Dictionary<int, int>();
        foreach (KeyValuePair<int, int> pair in punctCloseByOpen) openByClose[pair.Value] = pair.Key;
        for (int index = 0; index < tokens.Count; index++)
        {
            FaTok token = tokens[index];
            int paramOpen = -1;
            int paramClose = -1;
            int bodyStart = -1;
            int bodyEnd = -1;
            List<string> names = new List<string>();
            if (token.Kind == "word" && token.Value == "function")
            {
                paramOpen = Is(index + 1, "(") ? index + 1 : (K(index + 1) == "word" && Is(index + 2, "(") ? index + 2 : -1);
                if (paramOpen < 0 || !punctCloseByOpen.TryGetValue(paramOpen, out paramClose)) continue;
                int brace = paramClose + 1;
                int braceClose;
                if (!Is(brace, "{") || !punctCloseByOpen.TryGetValue(brace, out braceClose)) continue;
                bodyStart = paramOpen;
                bodyEnd = braceClose;
            }
            else if (token.Kind == "punct" && token.Value == "=>")
            {
                if (Is(index - 1, ")") && openByClose.TryGetValue(index - 1, out paramOpen)) { paramClose = index - 1; bodyStart = paramOpen; }
                else if (K(index - 1) == "word" && !Is(index - 2, ".")) { paramOpen = index - 2; paramClose = index; bodyStart = index - 1; names.Add(tokens[index - 1].Value); }
                else continue;
                int bodyFirst = index + 1;
                int closeBrace;
                if (Is(bodyFirst, "{") && punctCloseByOpen.TryGetValue(bodyFirst, out closeBrace)) bodyEnd = closeBrace;
                else bodyEnd = ExpressionBodyEnd(bodyFirst);
            }
            else if (token.Kind == "word" && Is(index + 1, "(") && !FaPs.CIn(token.Value, "if", "for", "while", "switch", "with", "function", "return", "typeof", "new", "await", "void", "delete", "in", "of", "else", "do", "case", "throw", "yield"))
            {
                paramOpen = index + 1;
                int braceClose;
                if (!punctCloseByOpen.TryGetValue(paramOpen, out paramClose) || !Is(paramClose + 1, "{") || !punctCloseByOpen.TryGetValue(paramClose + 1, out braceClose)) continue;
                bodyStart = paramOpen;
                bodyEnd = braceClose;
            }
            else continue;
            if (names.Count == 0)
            {
                for (int i = paramOpen + 1; i < paramClose; i++)
                {
                    if (tokens[i].Kind == "word" && keepNames.Contains(tokens[i].Value)) names.Add(tokens[i].Value);
                }
            }
            else
            {
                names = names.Where(n => keepNames.Contains(n)).ToList();
            }
            if (bodyEnd < bodyStart || bodyEnd >= tokens.Count) continue;
            FaFunctionScope scope = new FaFunctionScope();
            scope.Start = tokens[bodyStart].Start;
            scope.End = tokens[bodyEnd].End;
            scope.Names = names;
            scopes.Add(scope);
        }
        return scopes;
    }

    void ExpandInlineQueries()
    {
        if (inlineBindings.Count == 0) return;
        foreach (FaQuery query in ordered)
        {
            if (query.Expressions.Count == 0) continue;
            FaTemplateResult result = FaTemplateExpander.Expand(query.Text, query.Start, inlineBindings);
            if (result.Failed || string.Equals(result.Text, query.Text, StringComparison.Ordinal)) continue;
            query.Text = result.Text.Trim();
            query.Expressions = result.Expressions;
            if (query.Expressions.Count == 0 && string.Equals(query.Evidence, "DynamicTemplate", StringComparison.Ordinal)) query.Evidence = "StaticCandidate";
        }
    }

    // Interpolations that only carry data cannot declare VARs, columns or tables, so the dependency stage can treat them
    // as plain values instead of an opaque fragment.
    static readonly Regex MathCall = new Regex(@"^Math\.[A-Za-z]+\(", RegexOptions.CultureInvariant);
    static readonly Regex ReplaceCall = new Regex(@"^[A-Za-z_$][\w$]*\.(?:replace|replaceAll)\(", RegexOptions.CultureInvariant);
    static readonly Regex HelperCall = new Regex(@"^(?<name>[A-Za-z_$][\w$]*)\(", RegexOptions.CultureInvariant);
    HashSet<string> valueHelpers;

    static bool IsSingleCall(string expression)
    {
        int open = expression.IndexOf('(');
        if (open < 0 || expression[expression.Length - 1] != ')') return false;
        int level = 0;
        for (int i = open; i < expression.Length; i++)
        {
            char c = expression[i];
            if (c == '"' || c == '\'' || c == '`')
            {
                i++;
                while (i < expression.Length && expression[i] != c) { if (expression[i] == '\\') i++; i++; }
                continue;
            }
            if (c == '(') level++;
            else if (c == ')')
            {
                level--;
                if (level == 0) return i == expression.Length - 1;
            }
        }
        return false;
    }

    // A return expression that is plain computation (no text) or just escapes its parameter's text.
    bool IsValueReturn(int start, int end, string[] parameters)
    {
        if (start >= end) return false;
        bool arithmetic = false;
        for (int i = start; i < end; i++)
        {
            FaTok token = tokens[i];
            if (token.Kind == "string" || token.Kind == "template" || token.Kind == "regex") { arithmetic = false; break; }
            if (token.Kind == "punct" && FaPs.CIn(token.Value, "*", "+", "-", "/", "%")) arithmetic = true;
            if (token.Kind == "word" && FaPs.CIn(token.Value, "Math", "Date", "Number")) arithmetic = true;
        }
        if (arithmetic) return true;
        return K(start) == "word" && Array.IndexOf(parameters, tokens[start].Value) >= 0 && Is(start + 1, ".") &&
            In(start + 2, "replace", "replaceAll") && Is(start + 3, "(") && end == FindClose(start + 3) + 1;
    }

    int FindClose(int open)
    {
        int close;
        return punctCloseByOpen.TryGetValue(open, out close) ? close : -1;
    }

    bool IsValueBody(int bodyStart, string[] parameters)
    {
        if (bodyStart >= tokens.Count) return false;
        if (!Is(bodyStart, "{")) return IsValueReturn(bodyStart, ExpressionBodyEnd(bodyStart) + 1, parameters);
        int close = FindClose(bodyStart);
        if (close < 0) return false;
        int returns = 0;
        for (int index = bodyStart + 1; index < close; index++)
        {
            if (K(index) != "word" || !CIs(index, "return")) continue;
            int level = 0;
            int end = index + 1;
            while (end < close)
            {
                if (K(end) == "punct")
                {
                    if (In(end, "(", "[", "{")) level++;
                    else if (In(end, ")", "]", "}")) { if (level == 0) break; level--; }
                    else if (Is(end, ";") && level == 0) break;
                }
                end++;
            }
            if (!IsValueReturn(index + 1, end, parameters)) return false;
            returns++;
            index = end - 1;
        }
        return returns > 0;
    }

    HashSet<string> FindValueHelpers()
    {
        HashSet<string> helpers = new HashSet<string>(StringComparer.Ordinal);
        foreach (int site in inlineSites)
        {
            string name = tokens[site].Value;
            if (inlineBindingCounts[name] != 1 || site >= tokens.Count - 3) continue;
            if (CIs(site - 1, "function") && Is(site + 1, "("))
            {
                FaInlineParameters parsed = GetInlineParameters(site + 1);
                if (parsed != null && IsValueBody(parsed.Close + 1, parsed.Parameters)) helpers.Add(name);
            }
            else if ((CIn(site - 1, "const", "let", "var") || inlineDeclarators.Contains(site)) && Is(site + 1, "="))
            {
                int valueIndex = site + 2;
                if (Is(valueIndex, "("))
                {
                    FaInlineParameters parsed = GetInlineParameters(valueIndex);
                    if (parsed != null && Is(parsed.Close + 1, "=>") && IsValueBody(parsed.Close + 2, parsed.Parameters)) helpers.Add(name);
                }
                else if (K(valueIndex) == "word" && Is(valueIndex + 1, "=>") && IsValueBody(valueIndex + 2, new string[] { tokens[valueIndex].Value })) helpers.Add(name);
            }
        }
        return helpers;
    }

    // `{ ${value} }` is a DAX table constructor holding scalar values, which cannot declare variables, columns or tables.
    static bool AlwaysInsideBraces(string expression, string text)
    {
        string marker = "${" + expression + "}";
        int found = 0;
        int cursor = 0;
        int at;
        while ((at = text.IndexOf(marker, cursor, StringComparison.Ordinal)) >= 0)
        {
            int before = at - 1;
            while (before >= 0 && char.IsWhiteSpace(text[before])) before--;
            int after = at + marker.Length;
            while (after < text.Length && char.IsWhiteSpace(text[after])) after++;
            if (before < 0 || text[before] != '{' || after >= text.Length || text[after] != '}') return false;
            found++;
            cursor = at + marker.Length;
        }
        return found > 0;
    }

    bool IsValueExpression(string expression, string text)
    {
        string trimmed = expression.Trim();
        if (trimmed.Length == 0) return false;
        if ((MathCall.IsMatch(trimmed) || ReplaceCall.IsMatch(trimmed)) && IsSingleCall(trimmed)) return true;
        Match helper = HelperCall.Match(trimmed);
        if (helper.Success && IsSingleCall(trimmed))
        {
            if (valueHelpers == null) valueHelpers = FindValueHelpers();
            if (valueHelpers.Contains(helper.Groups["name"].Value)) return true;
        }
        if (trimmed.IndexOf('`') < 0 && AlwaysInsideBraces(expression, text)) return true;
        return false;
    }

    void ClassifyValueExpressions()
    {
        foreach (FaQuery query in ordered)
        {
            List<string> candidates = new List<string>(query.Expressions);
            foreach (string expression in query.Expressions) candidates.AddRange(FaTemplateExpander.NestedInterpolations(expression));
            foreach (string expression in candidates)
            {
                if (query.ValueExpressions.Contains(expression)) continue;
                // Nested interpolations sit in their parent expression's text; top-level ones in the query text.
                bool nested = !query.Expressions.Contains(expression);
                string context = nested ? string.Join("\n", query.Expressions.ToArray()) : query.Text;
                if (IsValueExpression(expression, context)) query.ValueExpressions.Add(expression);
            }
        }
    }

    static string StripValueInterpolations(string expression, List<string> valueExpressions)
    {
        foreach (string value in valueExpressions.OrderByDescending(v => v.Length)) expression = expression.Replace("${" + value + "}", " 0 ");
        return expression;
    }

    List<string> ExpressionNames(string expression)
    {
        List<string> found = new List<string>();
        Match head = ExpressionHead.Match(expression);
        if (head.Success) found.Add(head.Groups[1].Value);
        foreach (Match call in CalledName.Matches(expression)) found.Add(call.Groups[1].Value);
        List<string> result = new List<string>();
        HashSet<string> seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (string name in found)
        {
            if (IgnoredNames.Contains(name) || UpperName.IsMatch(name)) continue;
            if (seen.Add(name)) result.Add(name);
        }
        return result;
    }

    string DefinitionSnippet(int tokenIndex)
    {
        int snippetStart = Math.Max(0, tokens[tokenIndex].Start - 10);
        return FaPs.CollapseWhitespace(src.Substring(snippetStart, Math.Min(420, src.Length - snippetStart)));
    }

    string DescribeUnexpanded(string name, Dictionary<string, List<int>> sites, Dictionary<string, int> firstUse, int position)
    {
        FaImport importedFrom = moduleImports.FirstOrDefault(i => string.Equals(i.Local, name, StringComparison.Ordinal));
        // Minified names repeat across scopes, so describe the declaration that governs the query's position.
        FaDecl governing = null;
        List<FaDecl> candidates;
        if (FaOptions.Improved && declarationsByName.TryGetValue(name, out candidates))
        {
            foreach (FaDecl decl in candidates)
            {
                if (decl.Start <= position && position <= decl.End && (governing == null || decl.End - decl.Start < governing.End - governing.Start)) governing = decl;
            }
        }
        if (governing != null && governing.TokenIndex < 0) return "is a parameter of an enclosing function, so its value is only known at runtime";
        if (parameterNames.Contains(name) && !(FaOptions.Improved && inlineBindings.ContainsKey(name))) return "is a function parameter, so its value is only known at runtime";
        bool declared = sites.ContainsKey(name);
        if (governing != null)
        {
            sites = new Dictionary<string, List<int>>(StringComparer.OrdinalIgnoreCase);
            sites[name] = new List<int> { governing.TokenIndex };
            declared = true;
        }
        if (importedFrom != null && !declared)
        {
            return "is imported as '" + importedFrom.Name + "' from \"" + importedFrom.From + "\"; it is resolved when that file is captured and its definition is a template or a helper that returns one";
        }
        if (!declared)
        {
            string where = "no other use";
            int first;
            if (firstUse.TryGetValue(name, out first))
            {
                int firstStart = Math.Max(0, tokens[first].Start - 70);
                where = FaPs.CollapseWhitespace(src.Substring(firstStart, Math.Min(230, src.Length - firstStart)));
            }
            return "has no declaration in this script (built-in, imported or defined in another asset); first appears in: " + where;
        }
        List<int> list = sites[name];
        if (list.Count > 1) return "is declared " + list.Count + " times, so it cannot be tied to one definition; first: " + DefinitionSnippet(list[0]);
        if (inlineBindings.ContainsKey(name)) return "is an inlinable template, but this use was out of scope, passed an unsupported argument, or too deeply nested";
        int site = list[0];
        if (CIn(site - 1, "const", "let", "var") && Is(site + 1, "=") && !CIs(site + 2, "function") && !Is(site + 2, "(") &&
            !(K(site + 2) == "word" && Is(site + 3, "=>")))
        {
            string declaration = DefinitionSnippet(site);
            return "is a variable assigned from an expression, so it is a runtime value; declaration: " + declaration.Substring(0, Math.Min(120, declaration.Length));
        }
        return "is declared once but is not a single string/template or a function that only returns one; definition: " + DefinitionSnippet(site);
    }

    // Diagnostics for interpolations that could not be expanded: why each helper was skipped and a snippet of its
    // definition. Reported as UnexpandedSource on the query row.
    void BuildDiagnostics()
    {
        HashSet<string> unexpandedNames = new HashSet<string>(StringComparer.Ordinal);
        foreach (FaQuery query in ordered)
        {
            foreach (string expression in query.Expressions)
            {
                if (query.ValueExpressions.Contains(expression)) continue;
                foreach (string name in ExpressionNames(StripValueInterpolations(expression, query.ValueExpressions))) unexpandedNames.Add(name);
            }
        }
        // PowerShell hashtables compare keys case-insensitively, so names differing only in case share an entry.
        Dictionary<string, List<int>> diagnosticSites = new Dictionary<string, List<int>>(StringComparer.OrdinalIgnoreCase);
        Dictionary<string, int> firstUse = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);
        if (unexpandedNames.Count > 0)
        {
            for (int tokenIndex = 0; tokenIndex < tokens.Count; tokenIndex++)
            {
                FaTok token = tokens[tokenIndex];
                if (token.Kind != "word" || !unexpandedNames.Contains(token.Value)) continue;
                if (!firstUse.ContainsKey(token.Value)) firstUse[token.Value] = tokenIndex;
                if (tokenIndex == 0) continue;
                if (inlineDeclarators.Contains(tokenIndex) || CIn(tokenIndex - 1, "const", "let", "var", "function", "class") ||
                    (tokenIndex + 1 < tokens.Count && Is(tokenIndex + 1, "=>")))
                {
                    List<int> list;
                    if (!diagnosticSites.TryGetValue(token.Value, out list)) { list = new List<int>(); diagnosticSites[token.Value] = list; }
                    list.Add(tokenIndex);
                }
            }
        }
        foreach (FaQuery query in ordered)
        {
            List<string> notes = new List<string>();
            HashSet<string> seenNames = new HashSet<string>(StringComparer.Ordinal);
            foreach (string expression in query.Expressions)
            {
                if (query.ValueExpressions.Contains(expression)) continue;
                foreach (string name in ExpressionNames(StripValueInterpolations(expression, query.ValueExpressions)))
                {
                    if (notes.Count >= 6 || !seenNames.Add(name)) continue;
                    notes.Add(name + " " + DescribeUnexpanded(name, diagnosticSites, firstUse, query.Start));
                }
            }
            string joined = string.Join(" || ", notes.ToArray());
            if (joined.Length > 3000) joined = joined.Substring(0, 3000) + "...";
            query.UnexpandedSource = joined;
        }
    }

    class FaScopeEvent
    {
        public List<long> Add = new List<long>();
        public List<long> Remove = new List<long>();
    }

    int[] scopeStarts;
    List<FaRange> scopeOwners = new List<FaRange>();
    Dictionary<string, string> functionParents = new Dictionary<string, string>(StringComparer.Ordinal);

    void BuildScopes()
    {
        SortedDictionary<int, FaScopeEvent> scopeEvents = new SortedDictionary<int, FaScopeEvent>();
        Dictionary<long, FaRange> rangesByRank = new Dictionary<long, FaRange>();
        for (int rangeIndex = 0; rangeIndex < functionRanges.Count; rangeIndex++)
        {
            FaRange range = functionRanges[rangeIndex];
            // Preserve the original shortest-range rule, including first-match ties and inclusive ends.
            long rank = (long)(range.End - range.Start) * (functionRanges.Count + 1) + rangeIndex;
            rangesByRank[rank] = range;
            foreach (int position in new int[] { range.Start, range.End + 1 })
            {
                if (!scopeEvents.ContainsKey(position)) scopeEvents[position] = new FaScopeEvent();
            }
            scopeEvents[range.Start].Add.Add(rank);
            scopeEvents[range.End + 1].Remove.Add(rank);
        }
        SortedSet<long> activeRanges = new SortedSet<long>();
        List<int> scopePositions = new List<int>();
        foreach (KeyValuePair<int, FaScopeEvent> scopeEvent in scopeEvents)
        {
            foreach (long rank in scopeEvent.Value.Remove) activeRanges.Remove(rank);
            foreach (long rank in scopeEvent.Value.Add)
            {
                FaRange range = rangesByRank[rank];
                string parent = "-1";
                foreach (long candidateRank in activeRanges)
                {
                    FaRange candidate = rangesByRank[candidateRank];
                    if (candidate.End >= range.End)
                    {
                        parent = candidate.Start.ToString();
                        break;
                    }
                }
                functionParents[range.Start.ToString()] = parent;
            }
            foreach (long rank in scopeEvent.Value.Add) activeRanges.Add(rank);
            scopePositions.Add(scopeEvent.Key);
            scopeOwners.Add(activeRanges.Count > 0 ? rangesByRank[activeRanges.Min] : null);
        }
        scopeStarts = scopePositions.ToArray();
    }

    FaRange FunctionAt(int position)
    {
        int index = Array.BinarySearch(scopeStarts, position);
        if (index < 0) index = (~index) - 1;
        return index >= 0 ? scopeOwners[index] : null;
    }

    class FaAliasEntry
    {
        public string Value;
        public int Start;
        public int End;
        public int TokenIndex;
    }

    // Every declaration of a name that holds a connection alias: the alias declarations themselves and any other
    // declaration (parameter, destructured name, other variable) that would hide them.
    Dictionary<string, List<FaAliasEntry>> aliasEntries = new Dictionary<string, List<FaAliasEntry>>(StringComparer.Ordinal);

    void AddAliasDeclaration(string name, int start, int end, int tokenIndex, string value)
    {
        List<FaAliasEntry> list;
        if (!aliasEntries.TryGetValue(name, out list)) { list = new List<FaAliasEntry>(); aliasEntries[name] = list; }
        list.Add(new FaAliasEntry { Value = value, Start = start, End = end, TokenIndex = tokenIndex });
    }

    // Minified bundles reuse names, so a variable holding a connection alias is only the value declared in the
    // innermost scope that contains the use, and nothing nearer (a parameter, a destructured name) may redeclare it.
    void BuildAliasEntries()
    {
        HashSet<string> names = new HashSet<string>(StringComparer.Ordinal);
        for (int tokenIndex = 0; tokenIndex < tokens.Count - 2; tokenIndex++)
        {
            if (K(tokenIndex) == "word" && Is(tokenIndex + 1, "=") && K(tokenIndex + 2) == "string" && IdentifierValue.IsMatch(V(tokenIndex + 2)) &&
                (CIn(tokenIndex - 1, "const", "let", "var") || CIs(tokenIndex - 1, ","))) names.Add(tokens[tokenIndex].Value);
        }
        if (names.Count == 0) return;
        Stack<int> blocks = new Stack<int>();
        for (int tokenIndex = 0; tokenIndex < tokens.Count; tokenIndex++)
        {
            FaTok token = tokens[tokenIndex];
            if (token.Kind == "punct")
            {
                if (token.Value == "{") blocks.Push(tokenIndex);
                else if (token.Value == "}" && blocks.Count > 0) blocks.Pop();
                continue;
            }
            if (token.Kind != "word") continue;
            int blockStart = 0;
            int blockEnd = int.MaxValue;
            int close;
            if (blocks.Count > 0 && punctCloseByOpen.TryGetValue(blocks.Peek(), out close)) { blockStart = tokens[blocks.Peek()].Start; blockEnd = tokens[close].End; }
            if (names.Contains(token.Value) && (CIn(tokenIndex - 1, "const", "let", "var", "function", "class") || (CIs(tokenIndex - 1, ",") && Is(tokenIndex + 1, "="))))
            {
                string value = (Is(tokenIndex + 1, "=") && K(tokenIndex + 2) == "string" && IdentifierValue.IsMatch(V(tokenIndex + 2))) ? tokens[tokenIndex + 2].Value : null;
                AddAliasDeclaration(token.Value, blockStart, blockEnd, tokenIndex, value);
            }
            else if (CIn(tokenIndex, "const", "let", "var") && (Is(tokenIndex + 1, "{") || Is(tokenIndex + 1, "[")))
            {
                int patternClose;
                if (!punctCloseByOpen.TryGetValue(tokenIndex + 1, out patternClose)) continue;
                for (int i = tokenIndex + 2; i < patternClose; i++)
                {
                    if (tokens[i].Kind == "word" && names.Contains(tokens[i].Value)) AddAliasDeclaration(tokens[i].Value, blockStart, blockEnd, -1, null);
                }
            }
        }
        foreach (FaFunctionScope scope in CollectFunctionScopes(names))
        {
            foreach (string name in scope.Names) AddAliasDeclaration(name, scope.Start, scope.End, -1, null);
        }
    }

    string ResolveAliasVariable(string name, int position)
    {
        List<FaAliasEntry> list;
        if (!aliasEntries.TryGetValue(name, out list)) return null;
        FaAliasEntry best = null;
        bool conflict = false;
        foreach (FaAliasEntry entry in list)
        {
            if (position < entry.Start || position > entry.End) continue;
            if (best == null || entry.Start > best.Start || (entry.Start == best.Start && entry.End < best.End)) { best = entry; conflict = false; }
            else if (entry.Start == best.Start && entry.End == best.End) conflict = true;
        }
        return best == null || conflict ? null : best.Value;
    }

    string ResolveAlias(int tokenIndex)
    {
        if (tokenIndex < 0 || tokenIndex >= tokens.Count) return null;
        FaTok token = tokens[tokenIndex];
        string alias;
        if (token.Kind == "string" && IdentifierValue.IsMatch(token.Value)) return token.Value;
        if (token.Kind == "word" && FaOptions.Improved) return ResolveAliasVariable(token.Value, token.Start);
        if (token.Kind == "word" && aliasVariables.TryGetValue(token.Value, out alias)) return alias;
        return null;
    }

    Dictionary<int, Dictionary<string, List<string>>> dependenciesByFunction = new Dictionary<int, Dictionary<string, List<string>>>();

    Dictionary<string, List<string>> FunctionDependencies(FaRange range)
    {
        if (range == null) return new Dictionary<string, List<string>>(StringComparer.OrdinalIgnoreCase);
        Dictionary<string, List<string>> cached;
        if (dependenciesByFunction.TryGetValue(range.Start, out cached)) return cached;
        Dictionary<string, List<string>> dependencies = new Dictionary<string, List<string>>(StringComparer.OrdinalIgnoreCase);
        for (int index = range.OpenIndex + 1; index < range.CloseIndex - 2; index++)
        {
            if (!In(index, "const", "let", "var")) continue;
            int cursor = index + 1;
            while (cursor < range.CloseIndex)
            {
                if (K(cursor) != "word" || !Is(cursor + 1, "=")) break;
                string name = tokens[cursor].Value;
                int expressionStart = cursor + 2;
                int roundDepth = 0, squareDepth = 0, curlyDepth = 0;
                int expressionEnd = expressionStart;
                while (expressionEnd < range.CloseIndex)
                {
                    if (Is(expressionEnd, "(")) roundDepth++;
                    else if (Is(expressionEnd, ")")) roundDepth--;
                    else if (Is(expressionEnd, "[")) squareDepth++;
                    else if (Is(expressionEnd, "]")) squareDepth--;
                    else if (Is(expressionEnd, "{")) curlyDepth++;
                    else if (Is(expressionEnd, "}")) curlyDepth--;
                    if (roundDepth == 0 && squareDepth == 0 && curlyDepth == 0 && In(expressionEnd, ",", ";")) break;
                    expressionEnd++;
                }
                FaOrderedSet identifiers = new FaOrderedSet();
                for (int dependencyIndex = expressionStart; dependencyIndex < expressionEnd; dependencyIndex++)
                {
                    if (tokens[dependencyIndex].Kind == "word") identifiers.Add(tokens[dependencyIndex].Value);
                }
                dependencies[name] = identifiers.Items;
                if (expressionEnd >= range.CloseIndex || Is(expressionEnd, ";"))
                {
                    index = expressionEnd;
                    break;
                }
                cursor = expressionEnd + 1;
            }
        }
        dependenciesByFunction[range.Start] = dependencies;
        return dependencies;
    }

    Dictionary<string, List<FaQuery>> queryOwners = new Dictionary<string, List<FaQuery>>(StringComparer.OrdinalIgnoreCase);
    Dictionary<int, string> queryOwnerByStart = new Dictionary<int, string>();
    Dictionary<int, FaOrderedSet> queryAliases = new Dictionary<int, FaOrderedSet>();

    void BuildOwners()
    {
        Regex declarationPattern = new Regex(@"(?:(?:const|let|var)\s+|,)\s*(?<name>[a-zA-Z_$][\w$]*)\s*=\s*$", RegexOptions.CultureInvariant);
        Regex functionPattern = new Regex(@"function\s+(?<name>[a-zA-Z_$][\w$]*)\s*\(", RegexOptions.CultureInvariant);
        foreach (FaQuery query in ordered)
        {
            FaRange ownerFunction = FunctionAt(query.Start);
            string owner = ownerFunction != null ? ownerFunction.Name : query.Symbol;
            if (ownerFunction == null)
            {
                int literalIndex;
                if (literalTokenByStart.TryGetValue(query.Start, out literalIndex))
                {
                    if (Is(literalIndex - 1, "=") && K(literalIndex - 2) == "word") owner = tokens[literalIndex - 2].Value;
                }
                if (owner.StartsWith("query_", StringComparison.OrdinalIgnoreCase))
                {
                    int declarationStart = Math.Max(0, query.Start - 500);
                    string declarationPrefix = src.Substring(declarationStart, query.Start - declarationStart);
                    Match declarationMatch = declarationPattern.Match(declarationPrefix);
                    if (declarationMatch.Success) owner = declarationMatch.Groups["name"].Value;
                }
                if (owner.StartsWith("query_", StringComparison.OrdinalIgnoreCase))
                {
                    int prefixStart = Math.Max(0, query.Start - 20000);
                    string prefix = src.Substring(prefixStart, query.Start - prefixStart);
                    MatchCollection functionMatches = functionPattern.Matches(prefix);
                    if (functionMatches.Count > 0) owner = functionMatches[functionMatches.Count - 1].Groups["name"].Value;
                }
            }
            List<FaQuery> owned;
            if (!queryOwners.TryGetValue(owner, out owned)) { owned = new List<FaQuery>(); queryOwners[owner] = owned; }
            owned.Add(query);
            queryOwnerByStart[query.Start] = owner;
            queryAliases[query.Start] = new FaOrderedSet();
        }
    }

    void AddExpressionRoute(string alias, int startIndex, int endIndex, FaRange range)
    {
        if (string.IsNullOrEmpty(alias) || startIndex >= endIndex) return;
        Dictionary<string, List<string>> dependencies = FunctionDependencies(range);
        Stack<string> pendingSymbols = new Stack<string>();
        HashSet<string> seenSymbols = new HashSet<string>(StringComparer.Ordinal);
        for (int index = startIndex; index < endIndex; index++)
        {
            if (tokens[index].Kind == "word") pendingSymbols.Push(tokens[index].Value);
            FaQuery[] contained;
            if (queriesByToken.TryGetValue(index, out contained))
            {
                foreach (FaQuery query in contained) queryAliases[query.Start].Add(alias);
            }
        }
        while (pendingSymbols.Count > 0)
        {
            string symbol = pendingSymbols.Pop();
            if (!seenSymbols.Add(symbol)) continue;
            List<FaQuery> owned;
            if (queryOwners.TryGetValue(symbol, out owned))
            {
                foreach (FaQuery query in owned) queryAliases[query.Start].Add(alias);
            }
            List<string> symbolDependencies;
            if (dependencies.TryGetValue(symbol, out symbolDependencies))
            {
                foreach (string dependency in symbolDependencies) pendingSymbols.Push(dependency);
            }
        }
    }

    // Traces `connection:`/`model:` properties and `semanticModel(alias).query(...)` calls, including routes that
    // pass the alias or the query through wrapper-function parameters.
    void AddWrapperRoutes()
    {
        Dictionary<string, Dictionary<int, string>> wrapperParameterRoutes = new Dictionary<string, Dictionary<int, string>>(StringComparer.OrdinalIgnoreCase);
        Dictionary<string, List<FaModelRoute>> parameterizedModelRoutes = new Dictionary<string, List<FaModelRoute>>(StringComparer.OrdinalIgnoreCase);
        int[] legacyRoutePositions = legacyRouteSites.ToArray();
        foreach (FaRange range in functionRanges)
        {
            int site = Array.BinarySearch(legacyRoutePositions, range.OpenIndex + 1);
            if (site < 0) site = ~site;
            for (; site < legacyRoutePositions.Length; site++)
            {
                int index = legacyRoutePositions[site];
                if (index >= range.CloseIndex - 5) break;
                string alias = null;
                int aliasParameterIndex = -1;
                int queryStart = -1;
                int queryEnd;
                if (In(index, "connection", "model") && Is(index + 1, ":"))
                {
                    string routeProperty = tokens[index].Value;
                    alias = ResolveAlias(index + 2);
                    if (alias == null && FaPs.Eq(routeProperty, "model") && K(index + 2) == "word")
                    {
                        aliasParameterIndex = Array.IndexOf(range.Parameters, tokens[index + 2].Value);
                    }
                    string queryProperty = FaPs.Eq(routeProperty, "model") ? "dax" : "query";
                    for (int propertyIndex = index + 3; propertyIndex < Math.Min(range.CloseIndex, index + 40); propertyIndex++)
                    {
                        if (Is(propertyIndex, queryProperty) && Is(propertyIndex + 1, ":"))
                        {
                            queryStart = propertyIndex + 2;
                            break;
                        }
                    }
                }
                else if (Is(index, "semanticModel") && Is(index + 1, "("))
                {
                    alias = ResolveAlias(index + 2);
                    bool queryCall = Is(index + 3, ")") && Is(index + 4, ".") && Is(index + 5, "query") && Is(index + 6, "(");
                    if (alias != null && queryCall) queryStart = index + 7;
                    else if (FaOptions.Improved && alias == null && K(index + 2) == "word")
                    {
                        aliasParameterIndex = Array.IndexOf(range.Parameters, tokens[index + 2].Value);
                        if (aliasParameterIndex >= 0)
                        {
                            if (queryCall) queryStart = index + 7;
                            else
                            {
                                // `const client = semanticModel(model); ... client.query(text)` inside the same helper.
                                for (int scan = index + 3; scan < range.CloseIndex - 2; scan++)
                                {
                                    if (Is(scan, "query") && Is(scan - 1, ".") && Is(scan + 1, "(") && K(scan + 2) == "word" &&
                                        Array.IndexOf(range.Parameters, tokens[scan + 2].Value) >= 0)
                                    {
                                        queryStart = scan + 2;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
                if ((alias == null && aliasParameterIndex < 0) || queryStart < 0) continue;
                int roundDepth = 0, squareDepth = 0, curlyDepth = 0;
                queryEnd = queryStart;
                while (queryEnd < range.CloseIndex)
                {
                    if (Is(queryEnd, "(")) roundDepth++;
                    else if (Is(queryEnd, ")"))
                    {
                        if (roundDepth == 0 && squareDepth == 0 && curlyDepth == 0) break;
                        roundDepth--;
                    }
                    else if (Is(queryEnd, "[")) squareDepth++;
                    else if (Is(queryEnd, "]")) squareDepth--;
                    else if (Is(queryEnd, "{")) curlyDepth++;
                    else if (Is(queryEnd, "}"))
                    {
                        if (roundDepth == 0 && squareDepth == 0 && curlyDepth == 0) break;
                        curlyDepth--;
                    }
                    if (roundDepth == 0 && squareDepth == 0 && curlyDepth == 0 && Is(queryEnd, ",")) break;
                    queryEnd++;
                }
                if (alias != null) AddExpressionRoute(alias, queryStart, queryEnd, range);
                else
                {
                    List<FaModelRoute> routes;
                    if (!parameterizedModelRoutes.TryGetValue(range.Name, out routes)) { routes = new List<FaModelRoute>(); parameterizedModelRoutes[range.Name] = routes; }
                    FaModelRoute route = new FaModelRoute();
                    route.ParameterIndex = aliasParameterIndex;
                    route.QueryStart = queryStart;
                    route.QueryEnd = queryEnd;
                    route.QueryParameterIndex = (queryEnd == queryStart + 1 && K(queryStart) == "word") ? Array.IndexOf(range.Parameters, tokens[queryStart].Value) : -1;
                    route.Range = range;
                    routes.Add(route);
                }
                if (alias != null && queryEnd == queryStart + 1 && K(queryStart) == "word")
                {
                    int parameterIndex = Array.IndexOf(range.Parameters, tokens[queryStart].Value);
                    if (parameterIndex >= 0)
                    {
                        Dictionary<int, string> byParameter;
                        if (!wrapperParameterRoutes.TryGetValue(range.Name, out byParameter)) { byParameter = new Dictionary<int, string>(); wrapperParameterRoutes[range.Name] = byParameter; }
                        byParameter[parameterIndex] = alias;
                    }
                }
            }
        }
        foreach (KeyValuePair<string, List<FaModelRoute>> wrapper in parameterizedModelRoutes)
        {
            // Minified bundles reuse short names, so an unrelated `zl(...)` must not be taken for this wrapper.
            if (FaOptions.Improved && functionRanges.Count(f => string.Equals(f.Name, wrapper.Key, StringComparison.Ordinal)) != 1) continue;
            foreach (int index in CallSites(wrapper.Key))
            {
                if (index >= tokens.Count - 2) continue;
                if (!Is(index, wrapper.Key) || !Is(index + 1, "(") || (index > 0 && Is(index - 1, "function"))) continue;
                if (FaOptions.Improved && !CIs(index, wrapper.Key)) continue;
                FaArg[] arguments = ArgumentRanges(index + 1);
                FaRange callerRange = FunctionAt(tokens[index].Start);
                foreach (FaModelRoute route in wrapper.Value)
                {
                    if (route.ParameterIndex >= arguments.Length) continue;
                    FaArg aliasArgument = arguments[route.ParameterIndex];
                    if (aliasArgument.End != aliasArgument.Start + 1) continue;
                    string alias = ResolveAlias(aliasArgument.Start);
                    if (alias == null) continue;
                    if (route.QueryParameterIndex >= 0 && route.QueryParameterIndex < arguments.Length)
                    {
                        FaArg queryArgument = arguments[route.QueryParameterIndex];
                        AddExpressionRoute(alias, queryArgument.Start, queryArgument.End, callerRange);
                    }
                    else AddExpressionRoute(alias, route.QueryStart, route.QueryEnd, route.Range);
                }
            }
        }
        foreach (KeyValuePair<string, Dictionary<int, string>> wrapper in wrapperParameterRoutes)
        {
            foreach (int index in CallSites(wrapper.Key))
            {
                if (index >= tokens.Count - 2) continue;
                if (!Is(index, wrapper.Key) || !Is(index + 1, "(") || (index > 0 && Is(index - 1, "function"))) continue;
                FaRange range = FunctionAt(tokens[index].Start);
                int argumentIndex = 0;
                foreach (FaArg argument in ArgumentRanges(index + 1))
                {
                    string routeAlias;
                    if (wrapper.Value.TryGetValue(argumentIndex, out routeAlias)) AddExpressionRoute(routeAlias, argument.Start, argument.End, range);
                    argumentIndex++;
                }
            }
        }
    }

    Dictionary<string, FaRange> routeFunctions = new Dictionary<string, FaRange>(StringComparer.Ordinal);
    Dictionary<string, string> routeParents = new Dictionary<string, string>(StringComparer.Ordinal);
    Dictionary<string, FaRouteParameter[]> routeParameters = new Dictionary<string, FaRouteParameter[]>(StringComparer.Ordinal);
    Dictionary<string, FaOrderedSet> routeSummaries = new Dictionary<string, FaOrderedSet>(StringComparer.Ordinal);
    Dictionary<string, FaArg> routeDeclarations = new Dictionary<string, FaArg>(StringComparer.Ordinal);
    Dictionary<string, List<string>> routeBuilders = new Dictionary<string, List<string>>(StringComparer.Ordinal);
    Dictionary<string, FaOrderedSet> routeBuilderQueries = new Dictionary<string, FaOrderedSet>(StringComparer.Ordinal);
    Dictionary<string, List<FaArg>> routeReturns = new Dictionary<string, List<FaArg>>(StringComparer.Ordinal);
    Dictionary<string, HashSet<string>> routeShadowedParameters = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
    Dictionary<string, FaRouteNode> routeExpressions = new Dictionary<string, FaRouteNode>(StringComparer.Ordinal);
    Queue<FaRouteNode> routePendingExpressions = new Queue<FaRouteNode>();
    Queue<FaRouteValue> routePendingValues = new Queue<FaRouteValue>();
    Dictionary<int, string> routeScopeCache = new Dictionary<int, string>();

    string RouteScope(int position)
    {
        string scope;
        if (!routeScopeCache.TryGetValue(position, out scope))
        {
            FaRange owner = FunctionAt(position);
            scope = owner != null ? owner.Start.ToString() : "-1";
            routeScopeCache[position] = scope;
        }
        return scope;
    }

    FaRouteSymbol<T> FindRouteSymbol<T>(string name, string scope, Dictionary<string, T> table)
    {
        while (true)
        {
            string key = scope + "\0" + name;
            T value;
            if (table.TryGetValue(key, out value)) return new FaRouteSymbol<T> { Scope = scope, Value = value };
            if (scope == "-1") return null;
            scope = routeParents[scope];
        }
    }

    FaRouteNode GetRouteExpression(int start, int end, string scope, string kind)
    {
        string key = scope + "\0" + kind + "\0" + start + ":" + end;
        FaRouteNode node;
        if (!routeExpressions.TryGetValue(key, out node))
        {
            node = new FaRouteNode();
            node.Key = key;
            node.Start = start;
            node.End = end;
            node.Scope = scope;
            node.Kind = kind;
            routeExpressions[key] = node;
            routePendingExpressions.Enqueue(node);
        }
        return node;
    }

    void AddRouteValue(FaRouteNode node, string value)
    {
        if (node.ValueSet.Add(value))
        {
            node.Values.Add(value);
            routePendingValues.Enqueue(new FaRouteValue { Node = node, Value = value });
        }
    }

    void AddRouteDependency(FaRouteNode parent, FaRouteNode child, bool queriesOnly)
    {
        bool existing;
        if (!child.Dependents.TryGetValue(parent.Key, out existing)) child.Dependents[parent.Key] = queriesOnly;
        else if (!queriesOnly) child.Dependents[parent.Key] = false;
        foreach (string value in child.Values.ToArray())
        {
            if (!child.Dependents[parent.Key] || value.StartsWith("query|", StringComparison.Ordinal)) AddRouteValue(parent, value);
        }
    }

    List<string> GetRouteValues(int start, int end, string scope, string kind)
    {
        if (start >= end) return new List<string>();
        FaRouteNode root = GetRouteExpression(start, end, scope, kind);
        // Build each expression once; cyclic dependencies converge by propagating only new facts.
        while (routePendingExpressions.Count > 0)
        {
            FaRouteNode node = routePendingExpressions.Dequeue();
            if (node.Kind == "alias")
            {
                if (node.End != node.Start + 1) continue;
                if (K(node.Start) == "string")
                {
                    if (IdentifierValue.IsMatch(tokens[node.Start].Value)) AddRouteValue(node, "alias|" + tokens[node.Start].Value);
                    continue;
                }
            }
            for (int cursor = node.Start; cursor < node.End; cursor++)
            {
                FaTok token = tokens[cursor];
                if (node.Kind == "query" && (token.Kind == "string" || token.Kind == "template"))
                {
                    FaQuery[] contained;
                    if (queriesByToken.TryGetValue(cursor, out contained))
                    {
                        foreach (FaQuery query in contained) AddRouteValue(node, "query|" + query.Start);
                    }
                }
                if (token.Kind != "word" || (cursor > node.Start && In(cursor - 1, ".", "?."))) continue;
                HashSet<string> shadowed;
                if (routeShadowedParameters.TryGetValue(node.Scope, out shadowed) && shadowed.Contains(token.Value)) continue;
                int parameterIndex = -1;
                FaRouteParameter[] parameters;
                if (routeParameters.TryGetValue(node.Scope, out parameters))
                {
                    for (int p = 0; p < parameters.Length; p++)
                    {
                        if (string.Equals(parameters[p].Name, token.Value, StringComparison.Ordinal)) { parameterIndex = p; break; }
                    }
                }
                if (parameterIndex >= 0)
                {
                    AddRouteValue(node, "parameter|" + parameterIndex);
                    continue;
                }
                FaRouteSymbol<FaArg> declaration = FindRouteSymbol<FaArg>(token.Value, node.Scope, routeDeclarations);
                if (declaration != null)
                {
                    FaRouteNode child = GetRouteExpression(declaration.Value.Start, declaration.Value.End, declaration.Scope, node.Kind);
                    AddRouteDependency(node, child, false);
                    continue;
                }
                if (node.Kind == "query" && cursor + 1 < node.End && Is(cursor + 1, "("))
                {
                    FaRouteSymbol<List<string>> builder = FindRouteSymbol<List<string>>(token.Value, node.Scope, routeBuilders);
                    if (builder != null && builder.Value.Count == 1)
                    {
                        string builderScope = builder.Value[0];
                        FaOrderedSet builderQueries;
                        if (routeBuilderQueries.TryGetValue(builderScope, out builderQueries))
                        {
                            foreach (string value in builderQueries.Items.ToArray()) AddRouteValue(node, value);
                        }
                        List<FaArg> returns;
                        if (routeReturns.TryGetValue(builderScope, out returns))
                        {
                            foreach (FaArg returnRange in returns)
                            {
                                if (returnRange.Start >= returnRange.End) continue;
                                FaRouteNode returnChild = GetRouteExpression(returnRange.Start, returnRange.End, builderScope, "query");
                                AddRouteDependency(node, returnChild, true);
                            }
                        }
                    }
                }
            }
        }
        while (routePendingValues.Count > 0)
        {
            FaRouteValue entry = routePendingValues.Dequeue();
            foreach (KeyValuePair<string, bool> dependent in entry.Node.Dependents.ToArray())
            {
                if (!dependent.Value || entry.Value.StartsWith("query|", StringComparison.Ordinal)) AddRouteValue(routeExpressions[dependent.Key], entry.Value);
            }
        }
        return new List<string>(root.Values);
    }

    List<string> ResolveRouteArgument(string value, FaRouteCall call, string kind)
    {
        List<string> result = new List<string>();
        if (!value.StartsWith("parameter|", StringComparison.Ordinal)) { result.Add(value); return result; }
        int index = int.Parse(value.Substring(10));
        if (index < call.Arguments.Length)
        {
            FaArg argument = call.Arguments[index];
            if (argument.Start < argument.End && !(argument.End == argument.Start + 1 && CIs(argument.Start, "undefined")))
            {
                return GetRouteValues(argument.Start, argument.End, call.Caller, kind);
            }
        }
        FaRouteParameter[] calleeParameters;
        if (routeParameters.TryGetValue(call.Callee, out calleeParameters) && index < calleeParameters.Length)
        {
            FaArg defaultRange = calleeParameters[index].Default;
            if (defaultRange != null) return GetRouteValues(defaultRange.Start, defaultRange.End, routeParents[call.Callee], kind);
        }
        return result;
    }

    // Tracks query and connection parameters together through Rayfin hooks, including declared defaults and
    // explicit per-call overrides.
    void AddConnectionRoutes()
    {
        foreach (FaRange function in functionRanges)
        {
            string key = function.Start.ToString();
            routeFunctions[key] = function;
            string parent = functionParents[key];
            routeParents[key] = parent;
            string builderKey = parent + "\0" + function.Name;
            List<string> builderList;
            if (!routeBuilders.TryGetValue(builderKey, out builderList)) { builderList = new List<string>(); routeBuilders[builderKey] = builderList; }
            builderList.Add(key);
            routeSummaries[key] = new FaOrderedSet();
            List<FaRouteParameter> parameters = new List<FaRouteParameter>();
            bool supported = true;
            foreach (FaArg argument in ArgumentRanges(function.ParameterOpen))
            {
                if (argument.Start == argument.End) continue;
                if (K(argument.Start) != "word" || (argument.End > argument.Start + 1 && !Is(argument.Start + 1, "=")))
                {
                    supported = false;
                    break;
                }
                FaArg defaultRange = argument.End > argument.Start + 1 ? new FaArg { Start = argument.Start + 2, End = argument.End } : null;
                parameters.Add(new FaRouteParameter { Name = tokens[argument.Start].Value, Default = defaultRange });
            }
            if (supported) routeParameters[key] = parameters.ToArray();
            else
            {
                // Local expressions are still usable, but unsupported bindings must shadow outer symbols.
                HashSet<string> shadowed = new HashSet<string>(StringComparer.Ordinal);
                foreach (string name in function.Parameters) shadowed.Add(name);
                routeShadowedParameters[key] = shadowed;
            }
        }
        for (int index = 0; index < tokens.Count - 1; index++)
        {
            if (K(index) != "word" || !CIs(index, "return")) continue;
            string scope = RouteScope(tokens[index].Start);
            if (!routeFunctions.ContainsKey(scope)) continue;
            List<FaArg> returns;
            if (!routeReturns.TryGetValue(scope, out returns)) { returns = new List<FaArg>(); routeReturns[scope] = returns; }
            returns.Add(new FaArg { Start = index + 1, End = valueEndByStart[index + 1] });
        }
        for (int index = 1; index < tokens.Count - 2; index++)
        {
            if (K(index) != "word" || !Is(index + 1, "=") || !(CIn(index - 1, "const", "let", "var") || CIs(index - 1, ","))) continue;
            string scope = RouteScope(tokens[index].Start);
            if (scope != "-1" && index < routeFunctions[scope].OpenIndex) continue;
            routeDeclarations[scope + "\0" + tokens[index].Value] = new FaArg { Start = index + 2, End = valueEndByStart[index + 2] };
        }
        foreach (FaQuery query in ordered)
        {
            string owner = RouteScope(query.Start);
            if (owner == "-1") continue;
            FaOrderedSet owned;
            if (!routeBuilderQueries.TryGetValue(owner, out owned)) { owned = new FaOrderedSet(); routeBuilderQueries[owner] = owned; }
            owned.Add("query|" + query.Start);
        }
        for (int index = 0; index < tokens.Count - 4; index++)
        {
            if (K(index) != "punct" || !Is(index, "{")) continue;
            string scope = RouteScope(tokens[index].Start);
            if (!routeSummaries.ContainsKey(scope)) continue;
            Dictionary<string, FaArg> properties = new Dictionary<string, FaArg>(StringComparer.Ordinal);
            int cursor = index + 1;
            bool closed = false;
            while (cursor < tokens.Count)
            {
                if (Is(cursor, "}")) { closed = true; break; }
                if (FaOptions.Improved && Is(cursor, ".") && Is(cursor + 1, ".") && Is(cursor + 2, "."))
                {
                    // `{ connection: a, query: b, ...options }`: the spread cannot override the properties read here.
                    cursor = valueEndByStart[cursor + 3];
                    if (cursor < tokens.Count && Is(cursor, ",")) cursor++;
                    else if (cursor >= tokens.Count || !Is(cursor, "}")) break;
                    continue;
                }
                if (K(cursor) != "word" && K(cursor) != "string") break;
                string name = tokens[cursor].Value;
                int start, end;
                if (cursor + 1 < tokens.Count && Is(cursor + 1, ":")) { start = cursor + 2; end = valueEndByStart[start]; }
                else { start = cursor; end = cursor + 1; }
                if (properties.ContainsKey(name)) break;
                properties[name] = new FaArg { Start = start, End = end };
                cursor = end;
                if (cursor < tokens.Count && Is(cursor, ",")) cursor++;
                else if (cursor >= tokens.Count || !Is(cursor, "}")) break;
            }
            if (!closed || !properties.ContainsKey("connection") || !properties.ContainsKey("query")) continue;
            FaArg aliasRange = properties["connection"];
            FaArg queryRange = properties["query"];
            List<string> aliases = GetRouteValues(aliasRange.Start, aliasRange.End, scope, "alias");
            List<string> queryValues = GetRouteValues(queryRange.Start, queryRange.End, scope, "query");
            foreach (string alias in aliases)
            {
                foreach (string queryValue in queryValues)
                {
                    if (alias.StartsWith("alias|", StringComparison.Ordinal) && queryValue.StartsWith("query|", StringComparison.Ordinal))
                    {
                        queryAliases[int.Parse(queryValue.Substring(6))].Add(alias.Substring(6));
                    }
                    else routeSummaries[scope].Add(alias + "\0" + queryValue);
                }
            }
        }
        Dictionary<string, List<FaRouteCall>> callsByCallee = new Dictionary<string, List<FaRouteCall>>(StringComparer.Ordinal);
        HashSet<string> wrapperNames = new HashSet<string>(StringComparer.Ordinal);
        foreach (string key in routeParameters.Keys) wrapperNames.Add(routeFunctions[key].Name);
        for (int index = 0; index < tokens.Count - 2; index++)
        {
            FaTok token = tokens[index];
            if (token.Kind != "word" || !wrapperNames.Contains(token.Value) || !Is(index + 1, "(") ||
                (index > 0 && CIn(index - 1, "function", ".", "?."))) continue;
            string scope = RouteScope(token.Start);
            FaRouteSymbol<List<string>> builder = FindRouteSymbol<List<string>>(token.Value, scope, routeBuilders);
            if (builder != null && builder.Value.Count == 1 && routeSummaries.ContainsKey(builder.Value[0]))
            {
                string callee = builder.Value[0];
                List<FaRouteCall> calls;
                if (!callsByCallee.TryGetValue(callee, out calls)) { calls = new List<FaRouteCall>(); callsByCallee[callee] = calls; }
                calls.Add(new FaRouteCall { Caller = scope, Callee = callee, Arguments = ArgumentRanges(index + 1) });
            }
        }
        Queue<KeyValuePair<string, string>> pendingRoutes = new Queue<KeyValuePair<string, string>>();
        foreach (KeyValuePair<string, FaOrderedSet> summary in routeSummaries)
        {
            foreach (string route in summary.Value.Items.ToArray()) pendingRoutes.Enqueue(new KeyValuePair<string, string>(summary.Key, route));
        }
        while (pendingRoutes.Count > 0)
        {
            KeyValuePair<string, string> entry = pendingRoutes.Dequeue();
            string[] pair = entry.Value.Split('\0');
            List<FaRouteCall> calls;
            if (!callsByCallee.TryGetValue(entry.Key, out calls)) continue;
            foreach (FaRouteCall call in calls)
            {
                List<string> aliases = ResolveRouteArgument(pair[0], call, "alias");
                List<string> queryValues = ResolveRouteArgument(pair[1], call, "query");
                foreach (string alias in aliases)
                {
                    foreach (string queryValue in queryValues)
                    {
                        if (alias.StartsWith("alias|", StringComparison.Ordinal) && queryValue.StartsWith("query|", StringComparison.Ordinal))
                        {
                            queryAliases[int.Parse(queryValue.Substring(6))].Add(alias.Substring(6));
                        }
                        else if (routeSummaries.ContainsKey(call.Caller))
                        {
                            string route = alias + "\0" + queryValue;
                            if (routeSummaries[call.Caller].Add(route)) pendingRoutes.Enqueue(new KeyValuePair<string, string>(call.Caller, route));
                        }
                    }
                }
            }
        }
    }

    // The textual heuristics can attach an unrelated call's alias, so they run only when the structured trace
    // (explicit connection/model properties and traced parameters) found no model.
    void ApplyAliasHeuristics()
    {
        Regex modelObject = new Regex(@"model\s*:\s*[""'](?<route>[a-zA-Z_$][\w$]*)[""']\s*,\s*dax\s*:\s*$", RegexOptions.CultureInvariant);
        Regex assignmentPattern = new Regex(@"(?<symbol>[a-zA-Z_$][\w$]*)\s*=", RegexOptions.CultureInvariant);
        Regex firstAlias = new Regex(@"\G\s*[""'](?<route>[a-zA-Z_$][\w$]*)[""']\s*,", RegexOptions.CultureInvariant);
        Dictionary<string, FaOrderedSet> ownerAliasCache = new Dictionary<string, FaOrderedSet>(StringComparer.Ordinal);
        Dictionary<string, MatchCollection> routeMatchCache = new Dictionary<string, MatchCollection>(StringComparer.Ordinal);
        Dictionary<string, List<FaSourceCall>> sourceCallsByName = null;
        foreach (FaQuery query in ordered)
        {
            int queryPrefixStart = Math.Max(0, query.Start - 500);
            string queryPrefix = src.Substring(queryPrefixStart, query.Start - queryPrefixStart);
            FaOrderedSet aliasSet = queryAliases[query.Start];
            MatchCollection modelObjectMatches = modelObject.Matches(queryPrefix);
            if (modelObjectMatches.Count > 0) aliasSet.Add(modelObjectMatches[modelObjectMatches.Count - 1].Groups["route"].Value);
            bool heuristicFallback = aliasSet.Count == 0;
            MatchCollection wrapperMatches = WrapperCall.Matches(queryPrefix);
            if (heuristicFallback && wrapperMatches.Count > 0) aliasSet.Add(wrapperMatches[wrapperMatches.Count - 1].Groups["route"].Value);
            string owner = queryOwnerByStart[query.Start];
            if (heuristicFallback && owner.Length > 0 && !owner.StartsWith("query_", StringComparison.OrdinalIgnoreCase))
            {
                FaOrderedSet ownerAliases;
                if (!ownerAliasCache.TryGetValue(owner, out ownerAliases))
                {
                    ownerAliases = new FaOrderedSet();
                    if (sourceCallsByName == null)
                    {
                        sourceCallsByName = new Dictionary<string, List<FaSourceCall>>(StringComparer.Ordinal);
                        foreach (Match callMatch in Regex.Matches(src, @"(?<![\w$])(?<name>[a-zA-Z_$][\w$]*)\s*\("))
                        {
                            string name = callMatch.Groups["name"].Value;
                            List<FaSourceCall> sourceCalls;
                            if (!sourceCallsByName.TryGetValue(name, out sourceCalls)) { sourceCalls = new List<FaSourceCall>(); sourceCallsByName[name] = sourceCalls; }
                            Match aliasMatch = firstAlias.Match(src, callMatch.Index + callMatch.Length);
                            sourceCalls.Add(new FaSourceCall { Index = callMatch.Index, Alias = aliasMatch.Groups["route"].Value });
                        }
                    }
                    List<FaSourceCall> ownerCalls;
                    if (sourceCallsByName.TryGetValue(owner, out ownerCalls))
                    {
                        foreach (FaSourceCall ownerCall in ownerCalls)
                        {
                            if (ownerCall.Alias.Length > 0) ownerAliases.Add(ownerCall.Alias);
                            int assignmentStart = Math.Max(0, ownerCall.Index - 600);
                            string assignmentPrefix = src.Substring(assignmentStart, ownerCall.Index - assignmentStart);
                            MatchCollection assignmentMatches = assignmentPattern.Matches(assignmentPrefix);
                            if (assignmentMatches.Count == 0) continue;
                            string symbol = assignmentMatches[assignmentMatches.Count - 1].Groups["symbol"].Value;
                            MatchCollection routeMatches;
                            if (!routeMatchCache.TryGetValue(symbol, out routeMatches))
                            {
                                string routePattern = @"connection\s*:\s*[""'](?<route>[a-zA-Z_$][\w$]*)[""']\s*,\s*query\s*:\s*" + Regex.Escape(symbol) + @"(?![\w$])";
                                routeMatches = Regex.Matches(src, routePattern);
                                routeMatchCache[symbol] = routeMatches;
                            }
                            foreach (Match routeMatch in routeMatches) ownerAliases.Add(routeMatch.Groups["route"].Value);
                        }
                    }
                    ownerAliasCache[owner] = ownerAliases;
                }
                foreach (string alias in ownerAliases.Items) aliasSet.Add(alias);
            }
            query.ConnectionAliases = FaPs.SortedIgnoreCase(aliasSet.Items);
        }
    }



}

class FaAsset
{
    public Uri Uri;
    public string Path;
    public FaCatalog Catalog;
    public string DeferredSource;
}

// Port of Get-FabricAppDaxAssetScan: a cheap check that a script holds DAX-shaped text before it is parsed.
static class FaAssetScan
{
    const string EscapeText = @"\\(?:(?<continuation>\r\n)|u\{(?<hex>[0-9a-fA-F]{1,6})\}|u(?<hex>[0-9a-fA-F]{4})|x(?<hex>[0-9a-fA-F]{2})|(?<escaped>[\s\S]))";
    static readonly Regex Escapes = new Regex(EscapeText, RegexOptions.CultureInvariant);
    static readonly Regex References = new Regex(@"[""'`](?<path>(?:\.{0,2}/|https://)[^""'`\s]+\.m?js(?:\?[^""'`\s]*)?)[""'`]", RegexOptions.CultureInvariant);
    static readonly Regex DaxHeader = new Regex(@"(?i)\bEVALUATE\b(?=\s|/\*|--|\$\{|['""\[(])|\bDEFINE\b(?=\s|/\*|--|\$\{)", RegexOptions.CultureInvariant);
    static readonly Regex ModelOrField = new Regex(@"\b(?:semanticModels|field)[""']?\s*:", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex Literal = new Regex(@"""(?<text>(?:\\[\s\S]|[^""\\\r\n])*)""|'(?<text>(?:\\[\s\S]|[^'\\\r\n])*)'|`(?<text>(?:\\[\s\S]|[^`\\])*)`", RegexOptions.CultureInvariant);
    static readonly Regex EscapeHint = new Regex(@"\\[ux]", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex Measure = new Regex(@"^\[[A-Za-z_][^\]\r\n]*\]$", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex NotMeasure = new Regex(@"^\[object\s|[""'=\\<>]", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex QuotedTable = new Regex(@"'[^'\r\n]+'\s*\[", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex Reference = new Regex(@"(?<![\w'\]])\[[A-Za-z_][^\]\r\n]*\]", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex DaxCall = new Regex(@"(?<![\w.])[A-Z][A-Z0-9.]{2,}\s*\(", RegexOptions.CultureInvariant);

    static string Decode(Match match)
    {
        if (match.Groups["continuation"].Success) return "";
        if (match.Groups["hex"].Success)
        {
            int code = Convert.ToInt32(match.Groups["hex"].Value, 16);
            if (code <= 65535) return ((char)code).ToString();
            if (code <= 1114111) return char.ConvertFromUtf32(code);
            return match.Value;
        }
        string escaped = match.Groups["escaped"].Value;
        if (FaPs.In(escaped, "n", "r", "t", "f", "v")) return " ";
        if (escaped == "\r" || escaped == "\n") return "";
        return escaped;
    }

    public static bool NeedsParsing(string source)
    {
        string text = Escapes.Replace(source, new MatchEvaluator(Decode));
        bool needsParsing = DaxHeader.IsMatch(text) || ModelOrField.IsMatch(text);
        if (needsParsing) return true;
        // Inspect literals cheaply rather than mistaking JavaScript's define() or array indexing for DAX.
        foreach (Match literal in Literal.Matches(source))
        {
            string candidate = literal.Groups["text"].Value;
            if (candidate.IndexOf('[') < 0 && !EscapeHint.IsMatch(candidate)) continue;
            candidate = Escapes.Replace(candidate, new MatchEvaluator(Decode));
            if ((Measure.IsMatch(candidate) && !NotMeasure.IsMatch(candidate)) ||
                QuotedTable.IsMatch(candidate) ||
                (Reference.IsMatch(candidate) && DaxCall.IsMatch(candidate)))
            {
                return true;
            }
        }
        return false;
    }
}

// Port of Resolve-FabricAppImportedTemplates. Script files import constants and helpers from shared chunks; after every
// file of an app has been parsed, expand the interpolations that name an imported binding (following re-exports). A name
// the importing file also declares locally (a parameter, for example) is left alone because the use could be either.
class FaImportLinker
{
    Dictionary<string, FaAsset> byUri = new Dictionary<string, FaAsset>(StringComparer.Ordinal);
    Dictionary<string, Dictionary<string, FaBinding>> tables = new Dictionary<string, Dictionary<string, FaBinding>>(StringComparer.Ordinal);
    HashSet<string> building = new HashSet<string>(StringComparer.Ordinal);

    public static void Link(List<FaAsset> assets)
    {
        FaImportLinker linker = new FaImportLinker();
        foreach (FaAsset asset in assets) linker.byUri[asset.Uri.AbsoluteUri] = asset;
        foreach (FaAsset asset in assets)
        {
            FaCatalog catalog = asset.Catalog;
            if (catalog.Imports.Count == 0) continue;
            Dictionary<string, FaBinding> table = linker.GetTable(asset);
            foreach (FaQuery query in catalog.Queries)
            {
                if (query.Expressions.Count == 0) continue;
                FaTemplateResult result = FaTemplateExpander.Expand(query.Text, query.Start, table);
                if (result.Failed || string.Equals(result.Text, query.Text, StringComparison.Ordinal)) continue;
                query.Text = result.Text.Trim();
                query.Expressions = result.Expressions;
                if (query.Expressions.Count == 0 && string.Equals(query.Evidence, "DynamicTemplate", StringComparison.Ordinal)) query.Evidence = "StaticCandidate";
                if (!string.IsNullOrEmpty(query.UnexpandedSource))
                {
                    // Keep only the notes for names that are still unexpanded.
                    string remaining = string.Join("\n", query.Expressions.ToArray());
                    List<string> kept = new List<string>();
                    foreach (string note in Regex.Split(query.UnexpandedSource, @" \|\| "))
                    {
                        string name = note.Split(new char[] { ' ' }, 2)[0];
                        if (Regex.IsMatch(remaining, @"(?<![\w$.])" + Regex.Escape(name) + @"(?![\w$])")) kept.Add(note);
                    }
                    query.UnexpandedSource = string.Join(" || ", kept.ToArray());
                }
            }
        }
    }

    static void InitializeBindings(FaAsset asset)
    {
        if (asset.Catalog.BindingsDeferred) asset.Catalog = FaParser.Parse(asset.Catalog.DeferredSource, true);
    }

    Dictionary<string, FaBinding> GetTable(FaAsset asset)
    {
        string key = asset.Uri.AbsoluteUri;
        Dictionary<string, FaBinding> existing;
        if (tables.TryGetValue(key, out existing)) return existing;
        InitializeBindings(asset);
        FaCatalog catalog = asset.Catalog;
        Dictionary<string, FaBinding> table = new Dictionary<string, FaBinding>(StringComparer.Ordinal);
        foreach (KeyValuePair<string, FaBinding> pair in catalog.Bindings) table[pair.Key] = pair.Value;
        // A cycle of imports gets only the file's own bindings; the finished table is stored only when complete.
        if (!building.Add(key)) return table;
        try
        {
            HashSet<string> shadowed = new HashSet<string>(catalog.ShadowedNames, StringComparer.Ordinal);
            foreach (FaImport import in catalog.Imports)
            {
                if (table.ContainsKey(import.Local) || shadowed.Contains(import.Local)) continue;
                Uri providerUri;
                try { providerUri = new Uri(asset.Uri, import.From); }
                catch (Exception) { continue; }
                FaAsset provider;
                if (!byUri.TryGetValue(providerUri.AbsoluteUri, out provider)) continue;
                InitializeBindings(provider);
                string exported;
                if (!provider.Catalog.Exports.TryGetValue(import.Name, out exported)) continue;
                Dictionary<string, FaBinding> providerTable = GetTable(provider);
                FaBinding binding;
                if (!providerTable.TryGetValue(exported, out binding)) continue;
                if (FaOptions.Improved)
                {
                    // Only a file-level declaration can be exported.
                    while (binding != null && binding.ScopeEnd >= 0) binding = binding.Next;
                    if (binding == null) continue;
                }
                // Unscoped copy, whose own nested names resolve in the file that defines it.
                FaBinding copy = binding.Copy();
                copy.Next = null;
                copy.Excluded = null;
                copy.ScopeStart = 0;
                copy.ScopeEnd = -1;
                copy.Home = providerTable;
                table[import.Local] = copy;
            }
        }
        finally { building.Remove(key); }
        tables[key] = table;
        return table;
    }
}

// Reads the saved frontend scripts of each requested app, parses them, links imports across files and writes one JSON
// result per app. This replaces the PowerShell parsing loop of Get-FabricAppDaxCapture.
static class FabricAppExtractor
{
    const string Origin = "https://fabric-app.invalid";
    static readonly Regex HtmlHead = new Regex(@"^\s*(?:<!doctype\s+html|<html\b)", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex InlineScript = new Regex(@"<script\b(?<attributes>[^>]*)>(?<body>.*?)</script\s*>", RegexOptions.IgnoreCase | RegexOptions.Singleline | RegexOptions.CultureInvariant);
    static readonly Regex SourceAttribute = new Regex(@"\bsrc\s*=", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    static readonly Regex BaseElement = new Regex(@"<base\b", RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    public static string Run()
    {
        string requestPath = Environment.GetEnvironmentVariable("IMPACTIQ_FABRIC_APP_EXTRACT_REQUEST");
        if (string.IsNullOrEmpty(requestPath)) throw new Exception("IMPACTIQ_FABRIC_APP_EXTRACT_REQUEST is not set.");
        JObject request = JObject.Parse(File.ReadAllText(requestPath));
        JToken strictParity = request["strictParity"];
        FaOptions.Improved = strictParity == null || !(bool)strictParity;
        string outputPath = (string)request["outputPath"];
        JArray apps = new JArray();
        foreach (JToken appToken in (JArray)request["apps"])
        {
            JObject app = (JObject)appToken;
            JObject result = new JObject();
            result["key"] = (string)app["key"];
            try { ProcessApp((string)app["frontendRoot"], (int)app["maxAssets"], result); }
            catch (Exception ex) { result["error"] = ex.Message; }
            apps.Add(result);
        }
        JObject output = new JObject();
        output["apps"] = apps;
        using (StreamWriter file = new StreamWriter(outputPath, false, new UTF8Encoding(false)))
        using (JsonTextWriter writer = new JsonTextWriter(file))
        {
            output.WriteTo(writer);
        }
        return "Fabric App extract wrote " + apps.Count + " app result(s).";
    }

    static JObject QueryJson(FaQuery query)
    {
        JObject json = new JObject();
        json["symbol"] = query.Symbol;
        json["evidence"] = query.Evidence;
        json["text"] = query.Text;
        json["expressions"] = new JArray(query.Expressions.ToArray());
        json["valueExpressions"] = new JArray(query.ValueExpressions.Where(v => query.Expressions.Any(e => e == v || e.Contains("${" + v + "}"))).ToArray());
        json["connectionAliases"] = new JArray(query.ConnectionAliases.ToArray());
        json["unexpandedSource"] = query.UnexpandedSource;
        json["start"] = query.Start;
        json["line"] = query.Line;
        json["column"] = query.Column;
        return json;
    }

    static void ProcessApp(string frontendRoot, int maxAssets, JObject result)
    {
        List<string> warnings = new List<string>();
        List<string> messages = new List<string>();
        int assetCount = 0;
        int failedAssets = 0;
        int filteredAssets = 0;
        long scriptChars = 0;
        Stopwatch readWatch = new Stopwatch();
        Stopwatch parseWatch = new Stopwatch();
        Queue<Uri> pending = new Queue<Uri>();
        HashSet<string> seen = new HashSet<string>(StringComparer.Ordinal);
        Dictionary<string, string> localAssets = new Dictionary<string, string>(StringComparer.Ordinal);
        List<string> files = new List<string>();
        foreach (string file in Directory.EnumerateFiles(frontendRoot, "*", SearchOption.AllDirectories))
        {
            string extension = Path.GetExtension(file);
            if (FaPs.In(extension, ".js", ".mjs")) files.Add(file);
        }
        foreach (string file in files.OrderBy(f => f, StringComparer.CurrentCultureIgnoreCase))
        {
            string relativePath = file.Substring(frontendRoot.Length + 1);
            string[] segments = relativePath.Split('\\');
            for (int i = 0; i < segments.Length; i++) segments[i] = Uri.EscapeDataString(segments[i]);
            Uri asset = new Uri(new Uri(Origin + "/"), string.Join("/", segments));
            localAssets.Add(asset.AbsoluteUri, file);
            pending.Enqueue(asset);
        }
        string indexPath = Path.Combine(frontendRoot, "index.html");
        if (File.Exists(indexPath))
        {
            string html = File.ReadAllText(indexPath);
            foreach (Match script in InlineScript.Matches(html))
            {
                if (!SourceAttribute.IsMatch(script.Groups["attributes"].Value) && script.Groups["body"].Value.Trim().Length > 0) failedAssets++;
            }
            if (BaseElement.IsMatch(html)) failedAssets++;
        }
        List<FaAsset> assets = new List<FaAsset>();
        while (pending.Count > 0 && assetCount < maxAssets)
        {
            Uri uri = pending.Dequeue();
            if (!seen.Add(uri.AbsoluteUri)) continue;
            if (uri.GetLeftPart(UriPartial.Authority) != Origin || uri.UserInfo.Length > 0 || uri.Query.Length > 0 || uri.Fragment.Length > 0)
            {
                failedAssets++;
                continue;
            }
            assetCount++;
            try
            {
                string localPath = localAssets[uri.AbsoluteUri];
                string content;
                readWatch.Start();
                try { content = File.ReadAllText(localPath); }
                finally { readWatch.Stop(); }
                if (HtmlHead.IsMatch(content)) throw new Exception("Expected JavaScript, not HTML.");
                scriptChars += content.Length;
                Stopwatch assetWatch = Stopwatch.StartNew();
                parseWatch.Start();
                FaCatalog catalog;
                bool filtered = false;
                try
                {
                    if (FaAssetScan.NeedsParsing(content)) catalog = FaParser.Parse(content, false);
                    else
                    {
                        filtered = true;
                        filteredAssets++;
                        catalog = new FaCatalog();
                    }
                }
                finally { parseWatch.Stop(); }
                if (assetWatch.Elapsed.TotalSeconds >= 5)
                {
                    messages.Add(string.Format("parsed script '{0}' ({1:N0} KB) in {2:N1}s", Path.GetFileName(localPath), content.Length / 1024.0, assetWatch.Elapsed.TotalSeconds));
                }
                bool deferred = filtered || catalog.BindingsDeferred;
                FaAsset record = new FaAsset();
                record.Uri = uri;
                record.Path = localPath;
                record.Catalog = catalog;
                record.DeferredSource = deferred ? content : null;
                assets.Add(record);
            }
            catch (Exception ex)
            {
                failedAssets++;
                warnings.Add("script '" + uri.GetLeftPart(UriPartial.Path) + "' could not be inspected: " + ex.Message);
            }
        }
        Dictionary<string, FaAsset> catalogByUri = new Dictionary<string, FaAsset>(StringComparer.Ordinal);
        Queue<FaAsset> importPending = new Queue<FaAsset>();
        foreach (FaAsset asset in assets)
        {
            catalogByUri[asset.Uri.AbsoluteUri] = asset;
            if (asset.DeferredSource == null) importPending.Enqueue(asset);
        }
        while (importPending.Count > 0)
        {
            FaAsset consumer = importPending.Dequeue();
            foreach (FaImport import in consumer.Catalog.Imports.ToArray())
            {
                Uri providerUri;
                try { providerUri = new Uri(consumer.Uri, import.From); }
                catch (Exception) { continue; }
                FaAsset provider;
                if (!catalogByUri.TryGetValue(providerUri.AbsoluteUri, out provider) || provider.DeferredSource == null) continue;
                parseWatch.Start();
                try
                {
                    // A query-bearing module can require a helper-only chunk with no DAX header of its own.
                    string source = provider.DeferredSource;
                    provider.DeferredSource = null;
                    bool wasFiltered = !provider.Catalog.BindingsDeferred;
                    provider.Catalog = FaParser.Parse(source, true);
                    if (wasFiltered) filteredAssets--;
                    importPending.Enqueue(provider);
                }
                catch (Exception ex)
                {
                    failedAssets++;
                    warnings.Add("imported helper '" + provider.Uri.GetLeftPart(UriPartial.Path) + "' could not be inspected: " + ex.Message);
                }
                finally { parseWatch.Stop(); }
            }
        }
        Stopwatch linkWatch = Stopwatch.StartNew();
        try { FaImportLinker.Link(assets); }
        catch (Exception ex) { warnings.Add("imported templates could not be linked across script files: " + ex.Message); }
        linkWatch.Stop();
        JArray assetJson = new JArray();
        foreach (FaAsset asset in assets)
        {
            JObject json = new JObject();
            json["uri"] = asset.Uri.AbsoluteUri;
            json["path"] = asset.Path;
            JArray queryJson = new JArray();
            foreach (FaQuery query in asset.Catalog.Queries) queryJson.Add(QueryJson(query));
            json["queries"] = queryJson;
            JObject constants = new JObject();
            foreach (KeyValuePair<string, string> constant in asset.Catalog.Constants) constants[constant.Key] = constant.Value;
            json["constants"] = constants;
            json["fieldCatalog"] = new JArray(asset.Catalog.FieldCatalog.ToArray());
            assetJson.Add(json);
        }
        result["assetCount"] = assetCount;
        result["failedAssets"] = failedAssets;
        result["filteredAssets"] = filteredAssets;
        result["assetLimitReached"] = pending.Count > 0;
        result["scriptChars"] = scriptChars;
        result["readSeconds"] = readWatch.Elapsed.TotalSeconds;
        result["parseSeconds"] = parseWatch.Elapsed.TotalSeconds;
        result["linkSeconds"] = linkWatch.Elapsed.TotalSeconds;
        result["warnings"] = new JArray(warnings.ToArray());
        result["messages"] = new JArray(messages.ToArray());
        result["assets"] = assetJson;
    }
}

FabricAppExtractor.Run();

