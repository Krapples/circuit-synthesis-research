@echo off
rem Build native\orientation_synth.exe (target-directed encoder orientations over the cofactor constructor) and
rem native\fq_check.exe (feature-quotient and root-partition checks) and native\preduce_check.exe (exact partial
rem reductions and canonical normalization checks), MSVC C++20.
call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
cd /d "%~dp0"
if not exist build\orientation mkdir build\orientation
cl /nologo /std:c++20 /O2 /EHsc /W4 /Fobuild\orientation\ /Feorientation_synth.exe tools\orientation_synth.cpp || exit /b 1
cl /nologo /std:c++20 /O2 /EHsc /W4 /Fobuild\orientation\ /Fefq_check.exe tools\fq_check.cpp || exit /b 1
cl /nologo /std:c++20 /O2 /EHsc /W4 /Fobuild\orientation\ /Fepreduce_check.exe tools\preduce_check.cpp || exit /b 1
