# Translation-rank doubling: scalar ceiling proved, joint conjecture reduced

Continues [joint translation rank](joint_translation_rank_handoff.md), [five-gate Schur](five_mixed_rank_schur_handoff.md) and [exact rank ceilings](exact_mixed_rank_ceiling_handoff.md). Updated 2026-11-26. **L-clb-036 remains open.**

Summary:
- The **scalar** conjecture R_max(t) = 2^(t+1) − 2 is now proved for every t, by a two-line first-gate doubling argument. It is a paper proof with an exact replay; ChatGPT has not yet audited it independently.
- The **joint** conjecture J_t ≤ 2^(t+1) − 2 remains **open**. It is reduced exactly to a single direction-rank bound, and no counterexample has been found.
- The audit of the previous round's three results passed.
- A small Lean file checks the square-zero halving lemma and the doubling arithmetic.
- **Main implication:** this whole family of rank measures cannot exceed n − 1 AND gates. It is closed as a route to L-clb-036.

## 0. Notation

- R = GF(2)[Z_2^n] acts on Boolean functions by translation, with τ_v f(x) = f(x+v) and Δ_v = 1 + τ_v. Since Δ_v² = 1 + τ_2v = 0, every Δ_v is square-zero.
- m is the augmentation ideal, spanned by the Δ_v.
- ρ(f) = dim R f, where R f is the span of all translates of f.
- For a family F, RF = Σ R f and μ(F) = dim m RF.
- Every nonzero translation-invariant subspace contains the constant 1, because the socle is the constants.

The handoff quantities in this notation:
- For a single nonconstant f: R_mix(f) = ρ(f) − 2 (exact ceiling handoff, §1). Equivalently μ(f) = ρ(f) − 1.
- For the gate family: J_t = μ(G_1,…,G_t) − 1. The span of the mixed coefficient images is m RF modulo constants.
- On every sampled template, the generator count dim RF/mRF equals t exactly (replay line "generator count").

## 1. Audit of the previous round

| Result | Verdict | How checked |
|---|---|---|
| Joint update J_j = 2 + J + r + δ (joint handoff §2) | **Sound** | Re-derived from the component decomposition G = PQ + aQ + bP + ab. The 2×2 pivot on {a},{b} is invertible. In the Schur complement D = [[A,B],[Bᵀ,0]], projecting onto the fresh blocks has image row(B), and its kernel is AK + im B + U = AK + U, since im B ⊆ U. The coefficient convention c(P)ᵀx = p_x(0) is consistent with the outer-product correction. |
| Dependency-subspace symmetry (five-gate handoff) | **Sound** | Affine changes of the fresh pair (swap; z1z2 = z1(z1+z2+1) plus a translation inside span(e_z1, e_z2)) are invertible affine substitutions. They preserve every translation span and leave the other gates unchanged. Rank is invariant because ρ(f∘L) = ρ(f) for invertible affine L. |
| Last-gate Schur identity R_mix = 2 + 2r + s | **Consistent** | Agrees with the joint update: R_mix(G) − J_j = s − δ − (J − r) ≤ 0. Not re-derived independently beyond that. |

## 2. Theorem (scalar doubling)

**Theorem.** Every Boolean function computed by a circuit with t AND gates (XOR, NOT and constants free, so t is the multiplicative complexity) satisfies ρ(f) ≤ 2^(t+1). Equivalently R_mix(f) ≤ 2^(t+1) − 2. Monomial chains attain this, so R_max(t) = 2^(t+1) − 2 exactly.

**Corollary.** MC(f) ≥ log2 ρ(f) − 1. This generalises MC ≥ deg − 1, since ρ(f) ≥ 2^deg f.

**Proof.**

1. **Pullback.** A circuit gives f = T∘L for an affine L and a generic template T. Translates of f are (τ_{Lv} T)∘L, so ρ(f) ≤ ρ(T).
2. **Normalisation.** In the template, the first gate is G1 = (z1 + α·Y)(z2 + β·Y), with Y the extra inputs. An invertible linear substitution z1' = z1 + α·Y, z2' = z2 + β·Y makes G1 = z1z2 and preserves ρ. After this, z1 and z2 occur only through G1.
3. **First-gate identity.** Write H = A + yE with y = z1z2, where A and E do not depend on z1, z2. Let H' = A + yE with y a fresh variable, and let M' = R H'.
   - Translating H by (c1, c2, u) gives τ_u A + (z1+c1)(z2+c2) τ_u E.
   - Taking differences over c gives R H = φ(M') ⊕ z1𝓔 ⊕ z2𝓔, where φ(a + ye) = a + z1z2·e and 𝓔 = span{τ_u E} = Δ_y M'.
   - The sum is direct: decompose uniquely as p + z1q + z2r + z1z2s with p, q, r, s free of z1, z2. φ(M') occupies the (p, s) components, z1𝓔 occupies q and z2𝓔 occupies r.
   - Hence **ρ(H) = ρ(H') + 2 dim Δ_y R H'**.
4. **Halving.** Δ_y is square-zero and R H' is Δ_y-stable, so dim Δ_y R H' ≤ ρ(H')/2 (Lean `square_zero_restrict_halving`). Therefore ρ(H) ≤ 2ρ(H').
5. **Induction.** H' is a template with t − 1 gates, in which y is one more extra input: later gates read α·y, which is allowed. An affine output has ρ ≤ 2. Induction gives ρ ≤ 2^(t+1) (Lean `doubling_recursion`). ∎

The same computation applied to the whole family gives the identities used in §3:
- **dim RF = dim RF' + 2 dim Δ_y RF'**, and likewise **μ(F) = μ(F') + 2 dim Δ_y RF'**. Here F' = {y, G2', …, Gt'}.
- **Composition**, for h nonconstant on fresh variables: dim R F[y:=h] = dim RF + (ρ(h) − 2) dim Δ_y RF. The first-gate identity is the case h = z1z2, with ρ = 4.

## 3. Joint conjecture: exact reduction and status (OPEN)

Apply μ(F) = μ(F') + 2 dim Δ_y RF'. F' consists of t − 1 template gates plus an affine generator, and affine members add only constants to m RF'. The joint conjecture would therefore follow by induction from:

**Part 2 (open).** For the gate family F of an s-gate template and any direction v: dim Δ_v RF ≤ 2^s.

What is known about part 2:
- **Directions in W** = ker z1 ∩ ker z2 commute with the substitution, so induction covers them.
- **Mixed directions.** For gate 1 = (z1 + x)z2, the exact formula is dim Δ_x RF = dim 𝓔 + dim(𝓔 + Δ_w 𝓜_0), where 𝓜_0 = ker Δ_y on 𝓜 = RF' (probe-verified at t = 2, 3). The open step is to bound this by 2^s.
- **Halving alone is not enough.** It gives dim Δ_v RF ≤ (μ + g)/2 with g ≤ s generators, which leaves excess ≈ s/2 at each step. Compounded, this yields only the naive bound (t+1)2^t.
- **Composition shows part 2 is necessary up to constants.** The joint conjecture at t + 1 (with h = z z' substituted for an extra input) implies dim Δ_y RF ≤ 2^s + O(1). Part 2 and the joint conjecture are therefore essentially equivalent.

Proposed stronger invariant: dim m_V RF ≤ 2^(s+1) − 2^(s+1−dim V) for every subgroup V. It is proved for V ⊆ W and for a single function (Nakayama over R_V), and is open when V touches the fresh pair. Every sample satisfies it, many with equality at every dim V.

Search evidence (sampled; **not proof**):

| Search | Result |
|---|---|
| Replay `translation_doubling_check.py`, seed 20261126 | 223 templates over t ≤ 4 with m ≤ 3 extras. 2946 direction checks and 892 subgroup checks, all within bounds. Maximum μ is 3, 7, 15, 31, which equals 2^(t+1) − 1 (tight). |
| Hill climb maximising (direction excess, μ excess) | t = 3 (m = 2) and t = 4 (m = 2: 4 seeds × 400 steps; m = 3: 3 seeds × 300 steps). Best excess (0, 0) everywhere, so the bound is reached but never exceeded. |
| Previous round | Complete enumeration for t ≤ 5; samples at t = 6, 7 reach 126 and 254. |

## 4. Failed approaches (do not repeat)

1. **Local doubling** J_j ≤ 2J_{j−1} + 2 fails at rank-two gates (explicit control in the joint handoff §3).
2. **Naive family recursion** using halving plus generator count gives only (t+1)2^t (§3).
3. **Reduction to one output** fails: the joint rank can exceed every single-output mixed rank. Replay histogram at t = 4: J − max R_mix ∈ {0, 2, 4, 6}.
4. **Monomial spanning in ℓ-coordinates.** The joint space is spanned by ℓ-coordinate monomials in only 43/100 samples at t = 3 and 3/40 at t = 4, so no combinatorial monomial proof exists.
5. **Abstract module lemmas** of the form dim(aM + b·ker a) ≤ dim cM are false (take a = b). Direction and subgroup bounds alone are also insufficient: the Klein-four module M1^k ⊕ M2^k ⊕ M3^k satisfies all of them. The missing ingredient is the generator count, since gate families have at most s generators.
6. **Generator-inclusive recursion** b ≤ 2b'' + 3 is too weak by a factor of 2.

## 5. Implications for SAT restrictions and L-clb-036

- **Rank measures are capped at linear size.** ρ(f) ≤ 2^n, so the corollary gives at most MC ≥ n − 1. Every mixed or translation-rank measure in this family, scalar or joint, has the same cap. The mixed rank across any cut is ≤ 2^(min side). The best possible yield is the classical degree-type bound of about n AND gates.
- **Even a proof of the joint conjecture would not help.** It would only make the bound uniform over multiple outputs. It cannot give n^1.01, even after composing with our SAT restrictions, because restrictions only lower n.
- The **restriction ceiling** from the causal round (a sound charge on f_ρ is at most C(f_ρ)) still applies independently.
- **Recommendation:** close the translation-rank route to L-clb-036. What an unrestricted bound would still need is a measure that is not bounded by an exponential of the AND count, i.e. one that is not subadditive-multiplicative under a single AND. Rank and dimension measures over translation modules all double at most once per AND.
- For SAT-specific synthesis the theorem remains a cheap, sound lower bound: MC(f_ρ) ≥ ⌈log2 ρ(f_ρ)⌉ − 1. It can be computed from truth tables in O(n 2^n · ρ). It is never weaker than the degree bound.

## 6. Files and replay

| File | Scope |
|---|---|
| [translation_doubling_check.py](translation_doubling_check.py), [replay](translation_doubling_replay.txt) | S1 scalar identity (958), S2 ceiling and tightness, S3 family identities for dim RF and m RF (223), S4/S5 sampled joint, direction and subgroup bounds, S6 composition (50), S7 halving (4777), C1 joint-excess histogram. Deterministic: `python -B translation_doubling_check.py` reproduces the replay byte for byte. |
| [../lean/CircuitLemmas/TranslationHalving.lean](../lean/CircuitLemmas/TranslationHalving.lean) | `square_zero_halving`, `square_zero_restrict_halving`, `doubling_recursion`. No sorry, no native_decide, no new axioms. The first-gate identity itself is a hypothesis there; it is not formalised over the group algebra. |

Scope: there is no unrestricted superlinear result, no production change and no external submission. The scalar proof is new to this project; we make no claim of originality in the literature. Translation-rank and derivative-dimension bounds on multiplicative complexity are closely related to known degree and "dimension of derivative space" arguments.

## 7. Next

- Have ChatGPT audit the scalar proof (§2, step 3: directness and template preservation).
- If the joint conjecture is still wanted for completeness, attack part 2 through the mixed-direction formula and the generator count.
- Otherwise drop rank measures for L-clb-036 and look for measures that are not exponential in the AND count.
