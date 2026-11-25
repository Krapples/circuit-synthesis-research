"""Cooperative worker deadlines for Python search and interruptible CDCL."""

from _thread import interrupt_main
from contextlib import contextmanager
from contextvars import ContextVar
from threading import Event, Lock, Thread


_active_deadline = ContextVar('regional_deadline', default=None)


class Deadline:
    def __init__(self):
        self.lock = Lock()
        self.expired = False
        self.solver = None

    def expire(self):
        with self.lock:
            self.expired = True
            if self.solver is None:
                interrupt_main()
            else:
                self.solver.interrupt()

    def check(self):
        if self.expired:
            raise KeyboardInterrupt


@contextmanager
def cdcl_deadline(solver):
    deadline = _active_deadline.get()
    if deadline is None:
        yield None
        return
    with deadline.lock:
        deadline.check()
        deadline.solver = solver
    try:
        yield deadline
    finally:
        with deadline.lock:
            deadline.solver = None


def timed(seconds, job, on_timeout):
    done, deadline = Event(), Deadline()
    token = _active_deadline.set(deadline)

    def alarm():
        if not done.wait(seconds):
            deadline.expire()

    timer = Thread(target=alarm, daemon=True)
    try:
        try:
            timer.start()
            result = job()
        finally:
            done.set()
            timer.join()
        deadline.check()
        return result
    except KeyboardInterrupt:
        # The single alarm can arrive while the first join is waiting.
        done.set()
        timer.join()
        return {'status': 'TIMEOUT', **on_timeout()}
    finally:
        _active_deadline.reset(token)
