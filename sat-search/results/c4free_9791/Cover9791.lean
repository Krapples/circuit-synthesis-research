import Mathlib

namespace Cover9791

def edges : List (Fin 24 × Fin 24) :=
  [(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23),
    (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15),
    (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17),
    (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19),
    (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22),
    (12, 14), (12, 20), (12, 22), (12, 23)]

def cover (S : Finset (Fin 24)) : Prop :=
  ∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S

def matching : Fin 11 → Fin 24 × Fin 24 :=
  ![(0, 15), (1, 16), (2, 13), (3, 14), (4, 19), (5, 20),
    (6, 17), (7, 18), (8, 23), (10, 21), (11, 22)]

theorem matching_edge : ∀ i, matching i ∈ edges := by decide

theorem matching_disjoint : ∀ (i j : Fin 11) (z : Fin 24),
    (z = (matching i).1 ∨ z = (matching i).2) →
    (z = (matching j).1 ∨ z = (matching j).2) → i = j := by
  decide

theorem cover_lb (S : Finset (Fin 24)) (hS : cover S) : 11 ≤ S.card := by
  classical
  let choose (i : Fin 11) : Fin 24 := if (matching i).1 ∈ S then (matching i).1 else (matching i).2
  have hinj : Function.Injective choose := by
    intro i j h
    have either (k : Fin 11) : choose k = (matching k).1 ∨ choose k = (matching k).2 := by
      by_cases h : (matching k).1 ∈ S <;> simp [choose, h]
    exact matching_disjoint i j (choose i) (either i) (h.symm ▸ either j)
  have hin : Finset.univ.image choose ⊆ S := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
    by_cases h : (matching i).1 ∈ S
    · simp [choose, h]
    · simpa [choose, h] using (hS _ (matching_edge i)).resolve_left h
  have hc := Finset.card_le_card hin
  rw [Finset.card_image_of_injective _ hinj] at hc
  simpa using hc

theorem cover_ub : ∃ S : Finset (Fin 24), cover S ∧ S.card = 11 := by
  refine ⟨{13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23}, ?_⟩
  constructor
  · intro e he
    let S : Finset (Fin 24) := {13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23}
    have h : edges.all (fun z => decide (z.1 ∈ S ∨ z.2 ∈ S)) = true := by decide
    exact of_decide_eq_true ((List.all_eq_true.1 h) e he)
  · decide

end Cover9791
