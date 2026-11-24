# L-gct-086 exploration notes (2026-11-23)

**Statement.** There is a constant C such that for every n, every complex linear space L of
n×n matrices with perm(J + T) = n! for all T ∈ L has dim L ≤ C·n. Released at the desk as
`exhausted`: no proof found, and the numerical probe was not sharp enough to be evidence.

## Reformulation

perm(J + tT) = Σ_k (n−k)! · t^k · P_k(T), where P_k(T) is the sum of all k×k sub-permanents
of T. Since L is closed under scaling, L is level iff P_1, …, P_n all vanish on L.

* P_1(T) = sum of all entries.
* P_2(T) = ½ (s² − Σ r_i² − Σ c_j² + Σ T_ij²) with s, r_i, c_j the total, row and column sums.
  On its own this allows isotropic spaces of dimension about n²/2, so the bound has to
  come from the higher P_k (as the desk notes: the determinant analogue is quadratic).

## A 2n − 3 construction (checked numerically, n = 3..8)

T supported on row 1 ∪ column 1, with Σ_{j≥2} T_1j = 0 and T_11 + Σ_{i≥2} T_i1 = 0.
Only P_1 and P_2 can be non-zero on such T (a permutation uses at most one entry of row 1 and
one of column 1). P_1 = total sum = 0, and P_2 = (Σ_{j≥2} T_1j)(Σ_{i≥2} T_i1) = 0.
This may or may not be the construction behind L-gct-080, which is not public.

## Numerical probe (`level_spaces.py`)

Levenberg–Marquardt over d-dimensional subspaces, 22–33 random restarts, 11 workers.

| n | 2n−3 | largest d found | larger d tried |
|---|------|-----------------|----------------|
| 3 | 3 | 3 | 4–6 stuck (residual ~1e-1) |
| 4 | 5 | 4–5 nearly (1e-7, 1e-8) | 6–9 stuck (~1e-2) |
| 5 | 7 | 6 | 7–11 stuck (~1e-3 to 7e-3) |

**Limitation:** at n = 5 the probe failed at d = 7 although the construction above has
dimension 7. Extremal spaces are degenerate points (a factor of P_2 vanishes identically),
where least squares converges slowly and random starts rarely land. So "stuck" above 2n − 3
is weak evidence at best; it says nothing about n beyond 5 either way.

## Thoughts for anyone continuing

Supporting T on r rows ∪ r columns gives ambient dimension ≈ 2rn with only P_1..P_2r
surviving. The question is whether those 2r conditions always cost ≈ (2r − 2)n dimensions.
A structured (not random) search over such supports would test that far better than the
generic probe.
