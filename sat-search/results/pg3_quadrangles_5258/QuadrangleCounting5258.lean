import Mathlib
import PEqualNP.Defs

namespace Quadrangles5258

open PEqualNP.HeptadCover

def through (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => p ∈ singerLines3 l)

def hitting (Q : Finset (Fin 13)) (p : Fin 13) : Finset (Fin 13) :=
  (through p).filter (fun l => l ∉ missLines singerLines3 Q)

def good (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => p ∉ Q ∧ 3 ≤ (hitting Q p).card)

theorem through_card : ∀ p : Fin 13, (through p).card = 4 := by decide +kernel

theorem common_excluded_incidence (A B : Finset (Fin 13))
    (hB : B ∈ quadrangles singerLines3)
    (goodA : (good A).card ≥ 5)
    (hitB : ∀ p : Fin 13, p ∉ B → 2 ≤ (hitting B p).card) :
    ∃ p l : Fin 13, p ∈ singerLines3 l ∧ p ∉ A ∧ p ∉ B ∧
      l ∉ missLines singerLines3 A ∧ l ∉ missLines singerLines3 B := by
  have cardB : B.card = 4 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1).2
  have existP : ∃ p ∈ good A, p ∉ B := by
    by_contra! impossible
    have bound := Finset.card_le_card (show good A ⊆ B from impossible)
    rw [cardB] at bound
    omega
  obtain ⟨p, hp, hpB⟩ := existP
  obtain ⟨hpA, hbig⟩ := (Finset.mem_filter.mp hp).2
  have hsmall := hitB p hpB
  have bound : ((hitting A p) ∪ (hitting B p)).card ≤ 4 := by
    rw [← through_card p]
    exact Finset.card_le_card (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have sum := Finset.card_union_add_card_inter (hitting A p) (hitting B p)
  have hnonempty : ((hitting A p) ∩ (hitting B p)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨l, hl⟩ := hnonempty
  obtain ⟨hlA, hlB⟩ := Finset.mem_inter.mp hl
  obtain ⟨hlp, notA⟩ := Finset.mem_filter.mp hlA
  exact ⟨p, l, (Finset.mem_filter.mp hlp).2, hpA, hpB, notA, (Finset.mem_filter.mp hlB).2⟩

end Quadrangles5258
