import PEqualNP.MetaComplexity.Helpers.EdgeFnAnd

namespace Exclusive5020

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.EdgeFn

theorem four_with_exclusive_mate {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    {gs : List Gate} {o : ℕ} (L : Least (n + 1) f gs o) (v : Fin (n + 1))
    (hNC : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false))
    {p q mate : ℕ} {g : Gate} (hpq : p ≠ q)
    (hg : gs[p]? = some g) (hop : g.op = .and)
    (hpin : g.inputs = [v.val, n + 1 + mate] ∨ g.inputs = [n + 1 + mate, v.val])
    (hq : Reads gs q v.val) (only : ∀ k, Reads gs k (n + 1 + mate) → k = p) :
    Drop f v false 4 gs.length := by
  have hFn : ∃ x y, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hNC
    exact ⟨_, _, h⟩
  have hv : v.val ∈ g.inputs := by rcases hpin with h | h <;> simp [h]
  have hm : n + 1 + mate ∈ g.inputs := by rcases hpin with h | h <;> simp [h]
  have hp : Reads gs p v := ⟨g, hg, hv⟩
  have hmp : mate < p := by
    have h := (L.hcl p g hg).lt _ hm
    omega
  have hmLen : mate < gs.length := hmp.trans (reads_len hp)
  have hmq : mate ≠ q := by
    intro e
    exact L.no_tri hFn q p v hq hp ⟨g, hg, by rwa [← e]⟩
  have noOut : o ≠ n + 1 + mate := by
    intro e
    have hpLen := reads_len hp
    have hLast : gs.length - 1 < gs.length := by omega
    have hneq : o ≠ n + 1 + (gs.length - 1) := by omega
    obtain ⟨h, hl, hr⟩ := L.live hFn (gs.length - 1) hLast hneq
    have ht := reads_len hr
    omega
  have hpc := isC_reader L.hcl v p g hg hv false (Or.inr (by simp [fixBit, hop]))
  obtain ⟨r, hrp, hr, _⟩ := L.next v false hNC p (reads_len hp) hpc
  have hrq : r ≠ q := by
    intro e
    exact L.no_tri hFn p q v hp hq (by rwa [← e])
  have hcl' := andSwap_clean gs mate v L.hcl hmLen
  have hgp' : (andSwap gs mate v)[p]? = some g := by
    rw [andSwap_get_ne gs mate v p (by omega)]
    exact hg
  have hq' : Reads (andSwap gs mate v) q v := by
    obtain ⟨gq, hgq, hh⟩ := hq
    refine ⟨gq, ?_, hh⟩
    rw [andSwap_get_ne gs mate v q hmq.symm]
    exact hgq
  have hr' : Reads (andSwap gs mate v) r (n + 1 + p) := by
    obtain ⟨gr, hgr, hh⟩ := hr
    refine ⟨gr, ?_, hh⟩
    rw [andSwap_get_ne gs mate v r (by omega)]
    exact hgr
  have hm' : Reads (andSwap gs mate v) mate v :=
    ⟨_, andSwap_get_eq gs mate v hmLen, by simp⟩
  have hpc' := isC_reader hcl' v p g hgp' hv false (Or.inr (by simp [fixBit, hop]))
  have hliteral : ∀ x : Fin (n + 1) → Bool, x v = false → vl gs x v = false := by
    intro x hx
    rw [vl_input gs x v v.isLt]
    exact hx
  have h4 := and_core n f gs o p mate v g v L false hNC hg hop hpin
    (by have := v.isLt; omega) hmLen only noOut hliteral {mate, p, q, r} (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact rc_input false hm'
      · exact rc_input false ⟨g, hgp', hv⟩
      · exact rc_input false hq'
      · exact rc_of_reads hr' hpc')
  have hcard : ({mate, p, q, r} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hmq, show mate ≠ p by omega,
      show mate ≠ r by omega]), Finset.card_eq_three.2 ⟨p, q, r, hpq, by omega, hrq.symm, rfl⟩]
  rwa [hcard] at h4

end Exclusive5020
