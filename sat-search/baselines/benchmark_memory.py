"""Process-family commit cap for single-worker Windows benchmark replays."""

import ctypes as ct
from ctypes import wintypes
import os


def limit_commit_mib(mib):
    if mib <= 0:
        raise ValueError('memory limit must be positive')
    cap = mib * 1024 * 1024
    if os.name != 'nt':
        import resource
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
        return

    class BasicLimits(ct.Structure):
        _fields_ = [
            ('process_time', ct.c_int64), ('job_time', ct.c_int64), ('flags', wintypes.DWORD),
            ('min_ws', ct.c_size_t), ('max_ws', ct.c_size_t), ('processes', wintypes.DWORD),
            ('affinity', ct.c_size_t), ('priority', wintypes.DWORD), ('scheduling', wintypes.DWORD),
        ]

    class Limits(ct.Structure):
        _fields_ = [
            ('basic', BasicLimits), ('io', ct.c_uint64 * 6),
            ('process_commit', ct.c_size_t), ('job_commit', ct.c_size_t),
            ('peak_process', ct.c_size_t), ('peak_job', ct.c_size_t),
        ]

    kernel = ct.WinDLL('kernel32', use_last_error=True)
    kernel.CreateJobObjectW.argtypes = [ct.c_void_p, wintypes.LPCWSTR]
    kernel.CreateJobObjectW.restype = wintypes.HANDLE
    kernel.SetInformationJobObject.argtypes = [wintypes.HANDLE, ct.c_int, ct.c_void_p, wintypes.DWORD]
    kernel.GetCurrentProcess.restype = wintypes.HANDLE
    kernel.AssignProcessToJobObject.argtypes = [wintypes.HANDLE, wintypes.HANDLE]
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    job = kernel.CreateJobObjectW(None, None)
    if not job:
        raise ct.WinError(ct.get_last_error())
    limits = Limits()
    limits.basic.flags = 0x200  # JOB_OBJECT_LIMIT_JOB_MEMORY
    limits.job_commit = cap
    try:
        if not kernel.SetInformationJobObject(job, 9, ct.byref(limits), ct.sizeof(limits)):
            raise ct.WinError(ct.get_last_error())
        if not kernel.AssignProcessToJobObject(job, kernel.GetCurrentProcess()):
            raise ct.WinError(ct.get_last_error())
    finally:
        # A job remains active while a process is assigned to it.
        kernel.CloseHandle(job)
