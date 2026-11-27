import Mathlib

/-!
# Square-zero halving and the translation-rank doubling recursion

Foundational lemmas for `chatgpt_handoff/translation_doubling_handoff.md`.

* `square_zero_halving`: a square-zero endomorphism `D` of a finite-dimensional space `M`
  satisfies `2 * dim (D M) ≤ dim M`. For the translation group algebra over GF(2),
  `Δ_v = 1 + τ_v` has `Δ_v ^ 2 = 1 + τ_{2v} = 0`, and any translation-invariant module is
  `Δ_v`-stable, so `dim Δ_v M ≤ dim M / 2`.
* `square_zero_restrict_halving`: the same bound for a `D`-stable subspace.
* `doubling_recursion`: if `ρ_0 ≤ 2` and each step satisfies `ρ_(k+1) = ρ'_k + 2 d_k` with
  `2 d_k ≤ ρ'_k ≤ ρ_k` (first-gate identity plus halving plus the template being preserved),
  then `ρ_k ≤ 2 ^ (k + 1)`.
The first-gate identity itself is proved on paper and replayed by
`translation_doubling_check.py`; it is a hypothesis here.
-/

namespace CircuitLemmas.TranslationHalving

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A square-zero endomorphism has rank at most half the dimension. -/
theorem square_zero_halving (D : V →ₗ[K] V) (hD : D ∘ₗ D = 0) :
    2 * finrank K (LinearMap.range D) ≤ finrank K V := by
  have hle : LinearMap.range D ≤ LinearMap.ker D := by
    rintro _ ⟨x, rfl⟩
    have := congrArg (fun f => f x) hD
    simpa using this
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker D
  omega

/-- Halving for a `D`-stable subspace `M`: `2 * dim (D M) ≤ dim M`. -/
theorem square_zero_restrict_halving (D : V →ₗ[K] V) (hD : D ∘ₗ D = 0)
    (M : Submodule K V) (hM : ∀ x ∈ M, D x ∈ M) :
    2 * finrank K (M.map D) ≤ finrank K M := by
  let E : M →ₗ[K] M := D.restrict hM
  have hE : E ∘ₗ E = 0 := by
    ext x
    have := congrArg (fun f => f (x : V)) hD
    simpa [E] using this
  have h := square_zero_halving E hE
  have : finrank K (LinearMap.range E) = finrank K (M.map D) := by
    have hr : (LinearMap.range E).map M.subtype = M.map D := by
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply]
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨E ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    rw [← hr, Submodule.finrank_map_subtype_eq]
  omega

/-- The doubling recursion: first-gate identity plus halving gives `ρ_k ≤ 2^(k+1)`. -/
theorem doubling_recursion (ρ ρ' d : ℕ → ℕ) (h0 : ρ 0 ≤ 2)
    (hstep : ∀ k, ρ (k + 1) = ρ' k + 2 * d k)
    (hhalf : ∀ k, 2 * d k ≤ ρ' k) (hpre : ∀ k, ρ' k ≤ 2 ^ (k + 1)) :
    ∀ k, ρ k ≤ 2 ^ (k + 1) := by
  intro k
  cases k with
  | zero => simpa using h0
  | succ k =>
    have := hstep k
    have := hhalf k
    have := hpre k
    rw [pow_succ]
    omega

end CircuitLemmas.TranslationHalving
