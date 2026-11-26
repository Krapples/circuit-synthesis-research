import Mathlib
import PEqualNP.Outside.L_meta_7854

namespace Critical5258

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (w : ℕ) (x : List Bool) : Bool := (C.wires x).getD w false

def forcedFalse (C : Circuit) (q : ℕ) : Circuit :=
  ⟨C.gates.set q ⟨.or, []⟩, C.output⟩

def spec (n : ℕ) (C : Circuit) (a b : ℕ)
    (positive negative : Set (List Bool)) (r s : List Bool) : Prop :=
  Monotone2 C ∧ ReadsBack n C ∧
  (∀ x ∈ positive, val C a x = true ∧ val C b x = true) ∧
  (∀ x ∈ negative, (val C a x && val C b x) = false) ∧
  val C a r = true ∧ val C b s = true

/-- In a minimum-size realization, deletion of each gate loses a required
positive output on a common positive or on the chosen private row. -/
theorem gate_critical {n : ℕ} {C : Circuit} {a b : ℕ}
    {positive negative : Set (List Bool)} {r s : List Bool}
    (hp : ∀ x ∈ positive, List.length x = n)
    (hn : ∀ x ∈ negative, List.length x = n)
    (hr : r.length = n) (hs : s.length = n)
    (valid : spec n C a b positive negative r s)
    (minimal : ∀ D c d, spec n D c d positive negative r s → C.size ≤ D.size)
    {q : ℕ} (hq : q < C.size) :
    (∃ x ∈ positive, (val (forcedFalse C q) a x && val (forcedFalse C q) b x) = false) ∨
    val (forcedFalse C q) a r = false ∨ val (forcedFalse C q) b s = false := by
  classical
  by_contra! stable
  rcases stable with ⟨keep, keepR, keepS⟩
  obtain ⟨D, rename, hm, hb, smaller, sound⟩ :=
    PEqualNP.Outside.L_meta_7854 n C q valid.1 valid.2.1 hq
  change ∀ x w, x.length = n →
    val D (rename w) x = val (forcedFalse C q) w x ∧
    (val D (rename w) x = true → val C w x = true) at sound
  have validD : spec n D (rename a) (rename b) positive negative r s := by
    refine ⟨hm, hb, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [(sound x a (hp x hx)).1, (sound x b (hp x hx)).1]
      exact Bool.and_eq_true_iff.mp (Bool.eq_true_of_not_eq_false (keep x hx))
    · intro x hx
      apply Bool.eq_false_of_not_eq_true
      intro both
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp both
      have old := valid.2.2.2.1 x hx
      rw [(sound x a (hn x hx)).2 ha, (sound x b (hn x hx)).2 hb] at old
      contradiction
    · rw [(sound r a hr).1]
      exact Bool.eq_true_of_not_eq_false keepR
    · rw [(sound s b hs).1]
      exact Bool.eq_true_of_not_eq_false keepS
  exact Nat.not_lt_of_ge (minimal _ _ _ validD) smaller

end Critical5258
