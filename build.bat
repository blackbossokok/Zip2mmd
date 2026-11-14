@echo off
chcp 65001 >nul
title 构建 Zip2mmd
cd /d "%~dp0"

echo [1/2] 安装 / 检查 PyInstaller
python -m PyInstaller --version >nul 2>&1
if not errorlevel 1 goto build
python -m pip install pyinstaller
if errorlevel 1 goto fail

:build
echo.
echo [2/2] 打包单文件 exe
python -m PyInstaller --noconfirm --clean --onefile --noconsole --runtime-tmpdir . ^
  --name Zip2mmd --icon app.ico --version-file version.txt ^
  --add-data "vendor;vendor" --distpath dist --workpath _build --specpath _build app.py
if errorlevel 1 goto fail

echo.
echo 完成：dist\Zip2mmd.exe
pause
exit /b 0

:fail
echo.
echo 构建失败。
pause
exit /b 1
