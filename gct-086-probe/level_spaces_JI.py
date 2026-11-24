"""Numerical probe for L-gct-086: how large can a linear space L of n x n complex matrices be
with perm(J + T) = n! for every T in L?

A d-dimensional L is written as the row space of B = A0 + X A1, where [A0; A1] is a random
unitary change of coordinates on C^(n*n) (so every d-space is generically such a graph, and
B can never collapse to zero). We sample coefficient vectors c and drive the residuals
perm(J + sum_a c_a B_a) - n! to zero by Levenberg-Marquardt on X (the residuals are holomorphic
in X, so the complex Gauss-Newton step is the right one). Success = residual ~1e-10 on fresh
samples. This is evidence only: failure to find a space does not prove none exists.

Usage: python level_spaces.py <n> <d_min> <d_max> [restarts] [workers]
"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')   # one BLAS thread per worker; the Pool provides the parallelism
import sys, time, itertools
ITERS = 6000
from math import comb, factorial
import numpy as np
from multiprocessing import Pool


def ryser(M):
    """Permanents of a batch (S, m, m) by Ryser's formula."""
    S, m, _ = M.shape
    if m == 0:
        return np.ones(S, M.dtype)
    masks = np.array(list(itertools.product([0, 1], repeat=m))[1:], dtype=float)  # (2^m-1, m)
    signs = (-1.0) ** (m - masks.sum(1))
    sums = M @ masks.T                         # (S, m, 2^m-1): row sums over each column subset
    return np.prod(sums, axis=1) @ signs


def perm_and_minors(M):
    S, n, _ = M.shape
    p = ryser(M)
    G = np.empty((S, n, n), M.dtype)
    idx = np.arange(n)
    for j in range(n):
        rows = idx[idx != j]
        for k in range(n):
            cols = idx[idx != k]
            G[:, j, k] = ryser(M[:, rows][:, :, cols])
    return p, G


def attempt(args):
    n, d, seed, iters = args
    rng = np.random.default_rng(seed)
    N = n * n
    Q, _ = np.linalg.qr(rng.normal(size=(N, N)) + 1j * rng.normal(size=(N, N)))
    A0, A1 = Q[:, :d].T, Q[:, d:].T            # (d, N), (N-d, N)
    S = min(2 * comb(d + n, n), 6000)
    c = (rng.normal(size=(S, d)) + 1j * rng.normal(size=(S, d))) / np.sqrt(2 * d)
    X = 0.3 * (rng.normal(size=(d, N - d)) + 1j * rng.normal(size=(d, N - d)))
    J1 = np.ones((n, n)) + np.eye(n)
    target = float(round(ryser((np.ones((n, n)) + np.eye(n))[None].astype(complex))[0].real))
    lam = 1e-2

    def resid(X, c):
        B = A0 + X @ A1
        M = J1 + (c @ B).reshape(-1, n, n)
        p, G = perm_and_minors(M)
        return p - target, G

    r, G = resid(X, c)
    cost = np.vdot(r, r).real
    for it in range(iters):
        H = G.reshape(S, N) @ A1.T                       # (S, N-d)
        Jm = (c[:, :, None] * H[:, None, :]).reshape(S, -1)
        JhJ = Jm.conj().T @ Jm
        g = Jm.conj().T @ r
        while True:
            step = np.linalg.solve(JhJ + lam * np.diag(np.diag(JhJ).real + 1e-12), -g)
            Xn = X + step.reshape(d, N - d)
            rn, Gn = resid(Xn, c)
            cn = np.vdot(rn, rn).real
            if cn < cost:
                X, r, G, cost = Xn, rn, Gn, cn
                lam = max(lam / 3, 1e-12)
                break
            lam *= 4
            if lam > 1e12:
                break
        if cost < 1e-24 * S or lam > 1e12:
            break
        if it % 250 == 249:
            print(f'    [n={n} d={d} restart {seed % 1000:2d}] iter {it + 1:4d}  '
                  f'residual {np.sqrt(cost / S) / target:.1e}  damping {lam:.0e}', flush=True)
    # independent check on fresh samples
    c2 = (rng.normal(size=(500, d)) + 1j * rng.normal(size=(500, d))) / np.sqrt(2 * d)
    r2, _ = resid(X, c2)
    return float(np.max(np.abs(r2))) / target, it + 1


def main():
    n, dmin, dmax = map(int, sys.argv[1:4])
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 11
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 11
    print(f'n={n}: base J+I, ambient dimension {n * n}', flush=True)
    with Pool(workers) as pool:
        for d in range(dmin, dmax + 1):
            t = time.time()
            print(f'  d={d:2d}: starting {restarts} restarts at {time.strftime("%H:%M:%S")}', flush=True)
            res = []
            for r, its in pool.imap_unordered(attempt, [(n, d, 1000 * d + s, ITERS) for s in range(restarts)]):
                res.append((r, its))
                print(f'  d={d:2d}: restart {len(res):2d}/{restarts} done after {its:4d} iters, '
                      f'residual {r:.1e} (best so far {min(x for x, _ in res):.1e}, '
                      f'{time.time() - t:.0f}s)', flush=True)
            best = min(r for r, _ in res)
            verdict = 'FOUND ' if best < 1e-8 else 'nearly' if best < 1e-4 else 'stuck '
            print(f'  d={d:2d}: {verdict} best rel. residual {best:.1e} '
                  f'({sum(r < 1e-8 for r, _ in res)}/{restarts} restarts, {time.time() - t:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
