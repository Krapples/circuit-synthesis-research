@echo off
rem Build native\template_synth.exe (desk template units: exact AND/OR/NOT synthesis on cared rows) with MSVC.
rem CaDiCaL 2.2 is compiled from external\abc\src\sat\cadical (cadical_*.cpp + cadical_kitten.c) with the same
rem optimization flags, so whole-program optimization (/GL + /LTCG, MSVC's -flto) spans the solver too.
rem ABC defines match external\abc-build\build.ninja.
rem Optimization: /O2 /Ob3 /Oi /Ot (about -O3), /arch:AVX2 (Zen 3; MSVC has no -march=native), /GS- /Gy /DNDEBUG,
rem link /LTCG /OPT:REF /OPT:ICF. /Zi + /DEBUG only add a .pdb (used by the crash stack trace).
rem   build_template.bat          CaDiCaL objects are rebuilt only when missing
rem   build_template.bat clean    rebuild CaDiCaL objects too
call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
cd /d "%~dp0"
set ABC=%~dp0..\..\external\abc
set B=build\template
set OPT=/nologo /O2 /Ob3 /Oi /Ot /GL /Gy /GS- /arch:AVX2 /MD /utf-8 /Zi /DNDEBUG
set DEFS=/DWIN32 /DWINDOWS /D_CRT_SECURE_NO_WARNINGS /DABC_USE_PTHREADS /DHAVE_STRUCT_TIMESPEC /D_WINSOCKAPI_ /DABC_USE_STDINT_H=1
set INC=/I"%ABC%\src" /I"%ABC%\src\sat\cadical"
if "%1"=="clean" if exist %B% rmdir /s /q %B%
if not exist %B%\cadical mkdir %B%\cadical
if exist %B%\cadical\cadical_kitten.obj goto main
cl %OPT% /W0 /std:c++20 /EHsc /MP %DEFS% %INC% /c "%ABC%\src\sat\cadical\cadical_*.cpp" /Fo%B%\cadical\ /Fd%B%\cadical\vc.pdb || exit /b 1
cl %OPT% /W0 %DEFS% %INC% /c "%ABC%\src\sat\cadical\cadical_kitten.c" /Fo%B%\cadical\cadical_kitten.obj /Fd%B%\cadical\vck.pdb || exit /b 1
:main
cl %OPT% /W3 /std:c++20 /EHsc %DEFS% %INC% /c tools\template_synth.cpp /Fo%B%\template_synth.obj /Fd%B%\template_synth.pdb || exit /b 1
link /nologo /LTCG /OPT:REF /OPT:ICF /DEBUG /OUT:template_synth.exe %B%\template_synth.obj %B%\cadical\*.obj || exit /b 1
