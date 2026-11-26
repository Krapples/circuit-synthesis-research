import CircuitLemmas.GateElim

/-! Signed formula unfolding and operand-occurrence path counts for the AIG model. -/
namespace CircuitLemmas.GateElim
open Finset BigOperators

set_option maxHeartbeats 150000

inductive DeMorganFormula where
  | leaf (operand : Ref)
  | binary (isOr : Bool) (left right : DeMorganFormula)

namespace DeMorganFormula

def eval (x : ℕ → Bool) : DeMorganFormula → Bool
  | .leaf r => r.eval x
  | .binary isOr a b => if isOr then a.eval x || b.eval x else a.eval x && b.eval x

def neg : DeMorganFormula → DeMorganFormula
  | .leaf r => .leaf (r.negate true)
  | .binary isOr a b => .binary (!isOr) a.neg b.neg

def leaves : DeMorganFormula → ℕ
  | .leaf _ => 1
  | .binary _ a b => a.leaves + b.leaves

def internal : DeMorganFormula → ℕ
  | .leaf _ => 0
  | .binary _ a b => 1 + a.internal + b.internal

def depth : DeMorganFormula → ℕ
  | .leaf _ => 0
  | .binary _ a b => 1 + max a.depth b.depth

@[simp] theorem eval_neg (x : ℕ → Bool) (f : DeMorganFormula) : f.neg.eval x = !(f.eval x) := by
  induction f with
  | leaf r => simp [neg, eval, Ref.eval_negate]
  | binary t a b ia ib => cases t <;> simp [neg, eval, ia, ib]

@[simp] theorem internal_neg (f : DeMorganFormula) : f.neg.internal = f.internal := by
  induction f <;> simp_all [neg, internal]

@[simp] theorem depth_neg (f : DeMorganFormula) : f.neg.depth = f.depth := by
  induction f <;> simp_all [neg, depth]

theorem leaves_eq (f : DeMorganFormula) : f.leaves = 1 + f.internal := by
  induction f <;> simp_all [leaves, internal]; omega

theorem leaves_le_pow_depth (f : DeMorganFormula) : f.leaves ≤ 2 ^ f.depth := by
  induction f with
  | leaf r => simp [leaves, depth]
  | binary t a b ia ib =>
    have aa := Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left a.depth b.depth)
    have bb := Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right a.depth b.depth)
    simp only [leaves, depth, Nat.add_comm 1, pow_succ]
    omega

end DeMorganFormula

/-- Expand a reference from newest-first gates. Missing wires follow `val` and read false. -/
def unfoldRef (n : ℕ) : List Gate → Ref → DeMorganFormula
  | [], .wire w neg => if w < n then .leaf (.wire w neg) else .leaf (.const neg)
  | [], .const b => .leaf (.const b)
  | g :: gs, .wire w neg =>
      if w = n + gs.length then
        let f := DeMorganFormula.binary false (unfoldRef n gs g.a) (unfoldRef n gs g.b)
        if neg then f.neg else f
      else unfoldRef n gs (.wire w neg)
  | _ :: _, .const b => .leaf (.const b)

/-- Count paths from an internal wire to an output reference. The newest output contributes
one zero-edge path to itself, and the two operand slots contribute independently. -/
def outputPaths (n : ℕ) : List Gate → Ref → ℕ → ℕ
  | [], _, _ => 0
  | g :: gs, .wire w _, src =>
      if w = n + gs.length then
        (if src = w then 1 else 0) + outputPaths n gs g.a src + outputPaths n gs g.b src
      else outputPaths n gs (.wire w false) src
  | _ :: _, .const _, _ => 0

/-- Longest binary path in the output cone. -/
def outputDepth (n : ℕ) : List Gate → Ref → ℕ
  | [], _ => 0
  | g :: gs, .wire w _ =>
      if w = n + gs.length then 1 + max (outputDepth n gs g.a) (outputDepth n gs g.b)
      else outputDepth n gs (.wire w false)
  | _ :: _, .const _ => 0

theorem unfoldRef_eval (n : ℕ) (x : ℕ → Bool) (gs : List Gate) (r : Ref) :
    (unfoldRef n gs r).eval x = r.eval (val n x gs) := by
  induction gs generalizing r with
  | nil => cases r with
    | const b => rfl
    | wire w s => by_cases h : w < n <;> simp [unfoldRef, DeMorganFormula.eval, Ref.eval, val, h]
  | cons g gs ih =>
    cases r with
    | const b => rfl
    | wire w s =>
      by_cases h : w = n + gs.length
      · cases s <;> simp [unfoldRef, h, DeMorganFormula.eval, ih, Ref.eval, val, Gate.eval]
      · simpa [unfoldRef, h, Ref.eval, val] using ih (.wire w s)

theorem outputPaths_ge (n : ℕ) (gs : List Gate) (r : Ref) (src : ℕ)
    (h : n + gs.length ≤ src) : outputPaths n gs r src = 0 := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih =>
    have hlt : n + gs.length < src := by simp at h; omega
    cases r with
    | const b => rfl
    | wire w s =>
      by_cases hw : w = n + gs.length
      · simp [outputPaths, hw, show src ≠ n + gs.length by omega, ih _ (by omega)]
      · simp [outputPaths, hw, ih _ (by omega)]

theorem unfoldRef_internal (n : ℕ) (gs : List Gate) (r : Ref) :
    (unfoldRef n gs r).internal = ∑ i ∈ range gs.length, outputPaths n gs r (n+i) := by
  induction gs generalizing r with
  | nil =>
    cases r with
    | const b => simp [unfoldRef, DeMorganFormula.internal]
    | wire w s => by_cases h : w < n <;> simp [unfoldRef, h, DeMorganFormula.internal]
  | cons g gs ih =>
    cases r with
    | const b => simp [unfoldRef, DeMorganFormula.internal, outputPaths]
    | wire w s =>
      simp only [List.length_cons, sum_range_succ]
      by_cases hw : w = n + gs.length
      · have last : outputPaths n (g :: gs) (.wire w s) (n+gs.length) = 1 := by
          simp only [outputPaths, hw, ite_true, outputPaths_ge n gs _ _ (le_refl _),
            Nat.add_zero]
        have step : (∑ i ∈ range gs.length, outputPaths n (g :: gs) (.wire w s) (n+i)) =
            ∑ i ∈ range gs.length, (outputPaths n gs g.a (n+i) + outputPaths n gs g.b (n+i)) := by
          apply sum_congr rfl
          intro i hi
          have hil := mem_range.mp hi
          have hh : n + i ≠ n + gs.length := by omega
          simp only [outputPaths, hw, ite_true, ite_eq_right hh, Nat.zero_add]
        rw [last, step, sum_add_distrib, ← ih g.a, ← ih g.b]
        cases s <;> simp [unfoldRef, hw, DeMorganFormula.internal] <;> omega
      · have phase (i : ℕ) : outputPaths n gs (.wire w false) i =
            outputPaths n gs (.wire w s) i := by cases gs <;> rfl
        simp only [unfoldRef, ite_eq_right hw, outputPaths, phase,
          outputPaths_ge n gs _ _ (le_refl _), Nat.add_zero]
        exact ih (.wire w s)

theorem unfoldRef_depth (n : ℕ) (gs : List Gate) (r : Ref) :
    (unfoldRef n gs r).depth = outputDepth n gs r := by
  induction gs generalizing r with
  | nil => cases r with
    | const b => rfl
    | wire w s => by_cases h : w < n <;> simp [unfoldRef, h, DeMorganFormula.depth, outputDepth]
  | cons g gs ih =>
    cases r with
    | const b => rfl
    | wire w s =>
      by_cases h : w = n + gs.length
      · cases s <;> simp [unfoldRef, outputDepth, h, DeMorganFormula.depth, ih]
      · have phase : outputDepth n gs (.wire w s) = outputDepth n gs (.wire w false) := by
          cases gs <;> rfl
        simpa [unfoldRef, outputDepth, h, phase] using ih (.wire w s)

/-- The same unfolded formula realizes the circuit, has one more leaf than the total
internal path multiplicity, and obeys the binary-depth and size-times-multiplicity bounds. -/
theorem Circuit.unfold_paths (C : Circuit) (P : ℕ)
    (hp : ∀ i < C.size, outputPaths C.n C.rgates C.out (C.n+i) ≤ P) :
    ∃ f : DeMorganFormula, (∀ x, f.eval x = C.eval x) ∧
      f.leaves = 1 + ∑ i ∈ range C.size, outputPaths C.n C.rgates C.out (C.n+i) ∧
      f.leaves ≤ 2 ^ outputDepth C.n C.rgates C.out ∧ f.leaves ≤ 1 + C.size * P := by
  let f := unfoldRef C.n C.rgates C.out
  have hl : f.leaves = 1 + ∑ i ∈ range C.size, outputPaths C.n C.rgates C.out (C.n+i) := by
    rw [DeMorganFormula.leaves_eq, unfoldRef_internal, Circuit.size]
  refine ⟨f, (fun x => unfoldRef_eval C.n x C.rgates C.out), hl, ?_, ?_⟩
  · simpa [f, unfoldRef_depth] using f.leaves_le_pow_depth
  · rw [hl]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑ _i ∈ range C.size, P := sum_le_sum fun i h => hp i (mem_range.mp h)
      _ = C.size * P := by simp

end CircuitLemmas.GateElim
