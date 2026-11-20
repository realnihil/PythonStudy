@echo off
echo [Code Tutor] 오프라인 tree-sitter, pypdf, pymupdf 패키지 설치 중...
python -m pip install --no-index --find-links="%~dp0wheels" tree-sitter tree-sitter-c tree-sitter-cpp tree-sitter-javascript tree-sitter-typescript pypdf pymupdf
if errorlevel 1 (
    echo [오류] 설치에 실패했습니다. Python 버전(3.10~3.14, 64bit)을 확인하세요.
    pause
    exit /b 1
)
echo [완료] 설치가 끝났습니다. 이제 run_code_tutor.bat을 실행하세요.
pause
