@echo off
setlocal
set "IMPACTIQ_GUI_ROOT=%~dp0"
set "IMPACTIQ_GUI_COMMAND=try { & ([scriptblock]::Create([IO.File]::ReadAllText((Join-Path $env:IMPACTIQ_GUI_ROOT 'ImpactIQ GUI.txt')))) -LauncherRoot $env:IMPACTIQ_GUI_ROOT } catch { Add-Type -AssemblyName PresentationFramework; [void][System.Windows.MessageBox]::Show($_.Exception.Message, 'Impact IQ could not open', 'OK', 'Error'); exit 1 }"
rem The GUI starts with no console at all; -WindowStyle Hidden still opens a window when Windows Terminal is the default terminal.
powershell.exe -NoProfile -Command "$s = New-Object Diagnostics.ProcessStartInfo; $s.FileName = Join-Path $env:SystemRoot 'System32\WindowsPowerShell\v1.0\powershell.exe'; $s.Arguments = '-NoProfile -STA -EncodedCommand ' + [Convert]::ToBase64String([Text.Encoding]::Unicode.GetBytes($env:IMPACTIQ_GUI_COMMAND)); $s.UseShellExecute = $false; $s.CreateNoWindow = $true; [void][Diagnostics.Process]::Start($s)"
if errorlevel 1 (
    echo Impact IQ could not launch PowerShell. Check the error above and your organization's policy.
    pause
)
endlocal
