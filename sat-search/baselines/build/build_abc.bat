@echo off
rem Build an external tool with MSVC + Ninja. Set BUILD_SUBDIR (folder under external/) and optionally NINJA_TARGET.
call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
set "PATH=C:\Program Files\Microsoft Visual Studio\18\Community\Common7\IDE\CommonExtensions\Microsoft\CMake\Ninja;C:\Program Files\Microsoft Visual Studio\18\Community\Common7\IDE\CommonExtensions\Microsoft\CMake\CMake\bin;%PATH%"
cd /d "%~dp0..\..\..\external\%BUILD_SUBDIR%"
ninja -k 0 -j 22 %NINJA_TARGET%
