@echo off
rem Configure and build the Percy driver (sat-search/baselines/percy_driver) with MSVC + Ninja into external/percy-build.
call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
set "VSCM=C:\Program Files\Microsoft Visual Studio\18\Community\Common7\IDE\CommonExtensions\Microsoft\CMake"
set "PATH=%VSCM%\Ninja;%VSCM%\CMake\bin;%PATH%"
cd /d "%~dp0..\..\..\external"
if not defined PERCY_BUILD_DIR set "PERCY_BUILD_DIR=percy-build"
cmake -S "%~dp0..\percy_driver" -B "%PERCY_BUILD_DIR%" -G Ninja -DCMAKE_BUILD_TYPE=Release -DCMAKE_TRY_COMPILE_CONFIGURATION=Release -DCMAKE_POLICY_VERSION_MINIMUM=3.5 || exit /b 1
cmake --build "%PERCY_BUILD_DIR%" --target percy_run -j 8
