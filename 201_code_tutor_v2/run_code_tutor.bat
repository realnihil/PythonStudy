@echo off
cd /d "%~dp0"
where pythonw >nul 2>&1
if %errorlevel%==0 (
    start "" pythonw "%~dp0code_tutor.py" --serve
) else (
    start "" /min python "%~dp0code_tutor.py" --serve
)
