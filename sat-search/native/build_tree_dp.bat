@echo off
rem Build native\tree_dp.exe (exact small-excess tree DP for desk rect units) with MSVC.
rem Same optimization flags as build_template.bat (/O2 /Ob3 /GL + /LTCG /arch:AVX2 /DNDEBUG); no solver needed.
setlocal
call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
cd /d %~dp0
set OUT=%~1
if "%OUT%"=="" set OUT=tree_dp.exe
if not exist build\tree_dp mkdir build\tree_dp
cl /nologo /O2 /Ob3 /Oi /Ot /GL /Gy /GS- /arch:AVX2 /MD /utf-8 /Zi /DNDEBUG /W3 /std:c++20 /EHsc /c tools\tree_dp.cpp /Fobuild\tree_dp\tree_dp.obj /Fdbuild\tree_dp\ || exit /b 1
link /nologo /LTCG /OPT:REF /OPT:ICF /DEBUG /OUT:%OUT% build\tree_dp\tree_dp.obj || exit /b 1
