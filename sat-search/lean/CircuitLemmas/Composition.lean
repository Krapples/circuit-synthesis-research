/-
Block-restriction template (2026-11-26).

`xnorConj_restriction_lower`: if fixing a set `F` of essential inputs of `f` leaves exactly the XNOR
conjunction of `q ≥ 1` disjoint pairs, then `C(f) ≥ |F| + 4q - 1` in the free-NOT binary AIG model.

This is the shape of the six-bit SAT argument: with `n = 6q + 6`, the fragments `11x10y` and the tail
`110100` fix `|F| = 4q + 6` essential inputs and leave `F_q`, giving `B(SAT_n) ≥ 8q + 5`. The SAT-specific
premises (the string identity and the full support of `SAT_n`) are not formalized here.
-/
import CircuitLemmas.XnorConj
import CircuitLemmas.Excess

namespace CircuitLemmas.GateElim

theorem xnorConj_restriction_lower {n s : ℕ} {f : (ℕ → Bool) → Bool} (F : Finset ℕ) (b : ℕ → Bool)
    (P : List (ℕ × ℕ)) (hP : P ≠ []) (hlt : ∀ p ∈ P, p.1 < n ∧ p.2 < n) (hnd : PairsNodup P)
    (hFn : ∀ z ∈ F, z < n) (hess : ∀ z ∈ F, ∃ x, f (upd x z true) ≠ f (upd x z false))
    (hres : ∀ x, f (fixS F b x) = xnorConj P x) (h : Realizes n f s) :
    F.card + 4 * P.length ≤ s + 1 := by
  obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP
  have ht : Supp (p :: P') p.1 := ⟨p, List.mem_cons_self, Or.inl rfl⟩
  have hnc : ∃ x y, f (fixS F b x) ≠ f (fixS F b y) := by
    refine ⟨fun _ => false, upd (fun _ => false) p.1 (!false), ?_⟩
    rw [hres, hres, xnorConj_const, xnorConj_flip _ hnd _ ht false]
    decide
  obtain ⟨C, hn, hs, hf⟩ := excess_restriction F b hFn hess hnc h
  have := xnorConj_lower n _ _ rfl hlt hnd C hn (fun x => by rw [hf]; exact hres x)
  have hlen : 1 ≤ (p :: P').length := by simp
  omega

end CircuitLemmas.GateElim
