"""Run a prototype that uses Unix SIGALRM/setitimer deadlines on Windows.
Patches signal.SIGALRM -> SIGINT and signal.setitimer -> a threading.Timer that calls
_thread.interrupt_main(SIGINT), so the prototype's own alarm handler raises its Deadline in the main thread
(pure-Python code is interrupted at the next bytecode boundary). Then runs the module as __main__.
Usage: python experiments/win_deadline_run.py <module_dir> <module_name> [args...]"""
import _thread, runpy, signal, sys, threading, os

_timer = [None]


def setitimer(which, seconds, interval=0.0):
    if _timer[0] is not None:
        _timer[0].cancel(); _timer[0] = None
    if seconds > 0:
        t = threading.Timer(seconds, lambda: _thread.interrupt_main(signal.SIGINT)); t.daemon = True; t.start()
        _timer[0] = t
    return (0.0, 0.0)


if not hasattr(signal, 'SIGALRM'):
    signal.SIGALRM = signal.SIGINT
    signal.ITIMER_REAL = 0
    signal.setitimer = setitimer

if __name__ == '__main__':
    d, mod = sys.argv[1], sys.argv[2]
    sys.path.insert(0, os.path.abspath(d))
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    sys.path.append(os.path.join(here, 'theory'))     # fallback for modules not in <module_dir>
    sys.argv = [mod + '.py'] + sys.argv[3:]
    runpy.run_module(mod, run_name='__main__')
