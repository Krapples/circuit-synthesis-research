import Mathlib

namespace SatBridge.CubicPairWitness

abbrev Address (ι : Type*) := ι → Bool × Bool

def allowed (z : Address ι) : Prop := ∀ i, z i ≠ (true, true)

def evaluate (mix : (σ → Bool) → (ι → Bool)) (a b : ι → Bool) (x : σ → Bool) : Address ι :=
  fun i => (a i && b i && mix x i, a i && b i && !(mix x i))

theorem evaluate_allowed (mix : (σ → Bool) → (ι → Bool))
    (a b : ι → Bool) (x : σ → Bool) : allowed (evaluate mix a b x) := by
  intro i
  cases h : mix x i <;> simp [evaluate, h]

theorem exists_evaluate_iff (mix : (σ → Bool) → (ι → Bool))
    (surj : Function.Surjective mix) (z : Address ι) :
    (∃ a b x, evaluate mix a b x = z) ↔ allowed z := by
  constructor
  · rintro ⟨a, b, x, rfl⟩
    exact evaluate_allowed mix a b x
  · intro permitted
    obtain ⟨x, hx⟩ := surj (fun i => (z i).1)
    refine ⟨fun _ => true, fun i => (z i).1 || (z i).2, x, ?_⟩
    funext i
    have h := permitted i
    rcases hzi : z i with ⟨u, v⟩
    cases u <;> cases v <;> simp_all [evaluate]

theorem surjective_of_all_allowed (mix : (σ → Bool) → (ι → Bool))
    (all : ∀ z, allowed z → ∃ a b x, evaluate mix a b x = z) :
    Function.Surjective mix := by
  intro y
  obtain ⟨a, b, x, hx⟩ := all (fun i => (y i, !(y i))) (by
    intro i
    cases h : y i <;> simp [h])
  refine ⟨x, funext fun i => ?_⟩
  have eq := congrFun hx i
  cases ha : a i <;> cases hb : b i <;> cases hy : y i <;>
    cases hm : mix x i <;> simp_all [evaluate]

def translate (z shift : Address ι) : Address ι :=
  fun i => (Bool.xor (z i).1 (shift i).1, Bool.xor (z i).2 (shift i).2)

theorem trivial_period (shift : Address ι)
    (stable : ∀ z, allowed z → allowed (translate z shift)) :
    shift = fun _ => (false, false) := by
  classical
  funext i
  by_contra nonzero
  let z : Address ι := fun j => if j = i then (!(shift i).1, !(shift i).2) else (false, false)
  have hz : allowed z := by
    intro j
    by_cases h : j = i
    · subst j
      rcases hsi : shift i with ⟨u, v⟩
      cases u <;> cases v <;> simp_all [z]
    · simp [z, h]
  have h := stable z hz i
  rcases hsi : shift i with ⟨u, v⟩
  cases u <;> cases v <;> simp_all [translate, z]

end SatBridge.CubicPairWitness
