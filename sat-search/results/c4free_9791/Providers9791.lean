import Mathlib

namespace Providers9791

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

noncomputable def provided (S : Finset α) (x : α → Bool) : Bool := S.toList.any x

omit [DecidableEq α] in
theorem provided_true {S : Finset α} {x : α → Bool} :
    provided S x = true ↔ ∃ a ∈ S, x a = true := by
  simp [provided, List.any_eq_true]

/-- Free disjunctions whose terms meet a selected neighborhood in at most one
vertex cannot substitute for the raw input of one of that neighborhood's vertices. -/
theorem raw_left_needed (E : β → α → Prop)
    (f : (α → Bool) → (β → Bool) → Bool)
    (spec : ∀ l r, f l r = true ↔ ∃ b a, E b a ∧ l a = true ∧ r b = true)
    (providers : List (Finset α)) {a : α} {b : β} (hab : E b a)
    (mixed : ∀ S ∈ providers, a ∈ S → ∃ c ∈ S, ¬ E b c) :
    ∃ x y r, (∀ i ≠ a, x i = y i) ∧
      (∀ S ∈ providers, provided S x = provided S y) ∧
      f x r = false ∧ f y r = true := by
  classical
  let x : α → Bool := fun i => decide (¬ E b i)
  let y : α → Bool := Function.update x a true
  let r : β → Bool := fun j => decide (j = b)
  have agree : ∀ i ≠ a, x i = y i := by
    intro i hi
    rw [show y i = x i from Function.update_of_ne hi true x]
  refine ⟨x, y, r, agree, ?_, ?_, ?_⟩
  · intro S hS
    by_cases ha : a ∈ S
    · obtain ⟨c, hc, hbc⟩ := mixed S hS ha
      have hca : c ≠ a := fun e => hbc (e.symm ▸ hab)
      have hx : x c = true := by simp [x, hbc]
      rw [provided_true.2 ⟨c, hc, hx⟩, provided_true.2 ⟨c, hc, (agree c hca).symm.trans hx⟩]
    · apply (Bool.eq_iff_iff).2
      rw [provided_true, provided_true]
      constructor
      · rintro ⟨i, hi, hxi⟩
        exact ⟨i, hi, (agree i (fun he => ha (he ▸ hi))).symm.trans hxi⟩
      · rintro ⟨i, hi, hyi⟩
        exact ⟨i, hi, (agree i (fun he => ha (he ▸ hi))).trans hyi⟩
  · apply Bool.eq_false_of_not_eq_true
    intro h
    obtain ⟨j, i, hji, hi, hj⟩ := (spec x r).1 h
    have hj' : j = b := by simpa [r] using hj
    subst j
    exact (by simpa [x] using hi : ¬ E b i) hji
  · exact (spec y r).2 ⟨b, a, hab, by simp [y], by simp [r]⟩

omit [DecidableEq α] [DecidableEq β] in
theorem mixed_of_linear (E : β → α → Prop) {b : β} {a : α}
    (hab : E b a) (providers : List (Finset α))
    (linear : ∀ S ∈ providers, S.card ≥ 2 ∧
      ∀ i ∈ S, ∀ j ∈ S, E b i → E b j → i = j) :
    ∀ S ∈ providers, a ∈ S → ∃ c ∈ S, ¬ E b c := by
  intro S hS ha
  obtain ⟨size, unique⟩ := linear S hS
  by_contra! no
  have sub : S ⊆ {a} := by
    intro i hi
    simpa using unique i hi a ha (no i hi) hab
  have bound := Finset.card_le_card sub
  simp at bound
  omega

end Providers9791
