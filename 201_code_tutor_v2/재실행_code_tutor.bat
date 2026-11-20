@echo off
chcp 65001 >nul
powershell -NoProfile -Command "Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -like '*code_tutor.py*' } | ForEach-Object { Stop-Process -Id $_.ProcessId -Force }"
timeout /t 1 /nobreak >nul
start "" pythonw "%~dp0code_tutor.py" --serve
