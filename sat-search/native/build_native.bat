@echo off
rem Build the native regional completion extension (sat-search/native) with MSVC + Ninja.
rem From PowerShell: & "sat-search\native\build_native.bat"   (the '=' in 'P=NP' breaks plain cmd argument passing)
rem pybind11 lives in <repo>\external\pybind11-pip (pip install --target external/pybind11-pip "pybind11>=3.0").
call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
set "VSCM=C:\Program Files\Microsoft Visual Studio\18\Community\Common7\IDE\CommonExtensions\Microsoft\CMake"
set "PATH=%VSCM%\Ninja;%VSCM%\CMake\bin;%PATH%"
cd /d "%~dp0"
for /f "delims=" %%P in ('python -c "import sys;print(sys.executable)"') do set "PYEXE=%%P"
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release -DPython_EXECUTABLE="%PYEXE%" -Dpybind11_DIR="%~dp0..\..\external\pybind11-pip\pybind11\share\cmake\pybind11" || exit /b 1
cmake --build build -j 8 || exit /b 1
copy /y build\_regional_native*.pyd . >nul
