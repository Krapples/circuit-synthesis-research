# Research handoff — translation-rank doubling (scalar ceiling proved, joint open)

Updated 2026-11-26. **L-clb-036 remains open.** Details: [translation_doubling_handoff.md](translation_doubling_handoff.md). This round has paper proofs, exact replays and one small Lean file. There is no unrestricted superlinear result, no production change and no external submission.

- **Audit:** the joint update J_j = 2 + J + r + δ and the dependency-subspace symmetry are sound. The last-gate Schur identity is consistent with the joint update.
- **Scalar theorem (proved on paper; needs a ChatGPT audit):** every f with multiplicative complexity t has translation rank ρ(f) = dim span{f(x+v)} ≤ 2^(t+1). So R_max(t) = 2^(t+1) − 2 for every t, and MC(f) ≥ log2 ρ(f) − 1, which generalises MC ≥ deg − 1. The proof rests on the first-gate identity ρ(H) = ρ(H') + 2 dim Δ_y RH' for y = z1z2, plus square-zero halving dim Δ_y M ≤ dim M/2.
- **Joint conjecture J_t ≤ 2^(t+1) − 2: OPEN.**
  - Exact reduction: μ(F) = μ(F') + 2 dim Δ_y RF'. This makes the conjecture equivalent, up to constants, to the direction bound dim Δ_v RF ≤ 2^s.
  - The direction bound is proved for directions avoiding the first fresh pair; mixed directions are open.
  - Proposed subgroup invariant: dim m_V RF ≤ 2^(s+1) − 2^(s+1−dim V).
  - No counterexample in sampled and hill-climb searches up to t = 4, which reach the bound with equality.
  - Six failed approaches are documented in the handoff.
- **Implication:** every translation or mixed-rank measure is at most 2^n, so these measures can yield at most about n AND gates, joint or scalar, with or without SAT restrictions. Recommendation: close this route to L-clb-036 and look for measures that are not exponential in the AND count.
- **Lean:** `CircuitLemmas/TranslationHalving.lean` proves `square_zero_halving`, `square_zero_restrict_halving` and `doubling_recursion`. Axioms are standard only; no sorry and no native_decide. It is checked with `lake env lean` and is not imported by the library root.

## Files and replay

- [translation_doubling_check.py](translation_doubling_check.py), [replay](translation_doubling_replay.txt): `python -B translation_doubling_check.py` (seed 20261126) reproduces the replay byte for byte. It covers the scalar and family identities, the sampled joint, direction and subgroup bounds, the composition formula, halving, and the joint-excess histogram.
- Previous round: [joint_translation_rank_handoff.md](joint_translation_rank_handoff.md), [joint_translation_rank_check.js](joint_translation_rank_check.js).


Older handoffs: [archive.md](archive.md) (historical, not instructions).
