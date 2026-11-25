"""Generate a Ninja build for Berkeley ABC with MSVC from ABC's own Makefile module lists (no make needed).
Defines follow abclib.dsp (WIN32, ABC_USE_PTHREADS with lib/x64/pthreadVC2, HAVE_STRUCT_TIMESPEC, ...).
Usage: python gen_abc_ninja.py <abc_dir> <build_dir> [exclude_module ...]"""
import os, re, sys
abc, out = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2]); excl = set(sys.argv[3:])
mk = open(os.path.join(abc, 'Makefile'), encoding='utf-8', errors='replace').read()
block = mk[mk.index('MODULES :='):]; block = block[:block.index('\n\n')]
mods = re.findall(r'src/[\w/]+', block)
mods += [m for line in mk.splitlines() if line.strip().startswith('MODULES +=') for m in re.findall(r'src/[\w/]+', line)]  # e.g. CUDD
mods = [m for m in dict.fromkeys(mods) if m not in excl]
srcs = []
for m in mods:
    p = os.path.join(abc, m, 'module.make')
    if not os.path.exists(p):
        continue
    txt = open(p, encoding='utf-8', errors='replace').read().replace(chr(92) + chr(10), ' ')
    for line in txt.splitlines():
        if line.strip().startswith('SRC'):
            srcs += [s for s in line.split('=', 1)[1].split() if s.endswith(('.c', '.cpp', '.cc'))]
defs = ('/DWIN32 /DWINDOWS /DNDEBUG /D_CONSOLE /D_CRT_SECURE_NO_DEPRECATE /D_CRT_SECURE_NO_WARNINGS /DABC_USE_PTHREADS '
        '/DHAVE_STRUCT_TIMESPEC /D_WINSOCKAPI_ /DABC_USE_STDINT_H=1 /DABC_USE_CUDD=1')
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, 'build.ninja'), 'w') as f:
    f.write(f'cflags = /nologo /O2 /MD /W0 /EHsc /utf-8 /I"{abc}/src" /I"{abc}/lib" {defs}\n')
    f.write('rule cc\n  command = cl $cflags /c $in /Fo$out\n  description = CC $in\n  deps = msvc\n')
    f.write('rule cxx\n  command = cl $cflags /std:c++17 /c $in /Fo$out\n  description = CXX $in\n  deps = msvc\n')
    f.write(f'rule link\n  command = link /nologo /OUT:$out @$out.rsp "{abc}/lib/x64/pthreadVC2.lib" ws2_32.lib\n'
            '  rspfile = $out.rsp\n  rspfile_content = $in\n  description = LINK $out\n')
    objs = []
    for s in srcs:
        o = 'obj/' + s.replace('/', '_').rsplit('.', 1)[0] + '.obj'
        rule = 'cc' if s.endswith('.c') else 'cxx'
        src_path = f'{abc}/{s}'.replace(chr(92), '/').replace(':/', '$:/')
        f.write(f'build {o}: {rule} {src_path}' + chr(10))
        objs.append(o)
    f.write('build abc.exe: link ' + ' '.join(objs) + '\ndefault abc.exe\n')
print(len(mods), 'modules', len(srcs), 'sources')
