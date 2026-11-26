@echo off
rem Build native\cofactor_synth.exe (constructive cofactor two-signal upper bounds) with MSVC C++20.
call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
cd /d "%~dp0"
if not exist build\cofactor mkdir build\cofactor
cl /nologo /std:c++20 /O2 /EHsc /W4 /Fobuild\cofactor\ /Fecofactor_synth.exe tools\cofactor_synth.cpp || exit /b 1
