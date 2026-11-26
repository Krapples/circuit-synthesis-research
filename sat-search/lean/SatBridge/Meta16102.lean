/-
L-meta-16102: kernel-checked pieces of the refutation (2026-11-26).

This file is NOT a proof that the posted L-meta-16102 statement is false. It checks two reusable
pieces of the paper argument in `sat-search/results/mid_not_16102`, stated for the upstream
circuit model (`PEqualNP.CircuitLowerBounds`):

* `sandwich`: in an AND/OR/NOT circuit with at most one NOT gate, overriding that gate's output
  with a free bit `y` gives a function `G x y` that is monotone in `x` and `y`. The real output is
  `G x v` for some bit `v`, so `G x false ≤ C.eval x ≤ G x true`.
* `f16102_mono`: the posted truth table is monotone in each input. `f16102_witness` gives two
  inputs that show it is not constant.

The unformalized parts are the eight-binary-gate lower bound (fork counting, read-once lemma and
a 12.8M-comparison formula DP) and the nine-gate core (22 DRUP-certified SAT shards). See
`core9_certificate_audit.md` for the obstruction to formalizing them within upstream limits.
-/
import PEqualNP.Defs

namespace SatBridge.Meta16102

open PEqualNP.CircuitLowerBounds

/-- Whether an operation is NOT (`GateOp` has no `DecidableEq`). -/
def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

/-- The operation is AND, OR or NOT. -/
def AndOrNot : GateOp → Prop
  | GateOp.and => True
  | GateOp.or => True
  | GateOp.not => True
  | _ => False

/-- The upstream wire step. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The wire step with every NOT gate's value replaced by `y`. -/
def stepY (y : Bool) (w : List Bool) (g : Gate) : List Bool :=
  w ++ [if isNot g.op then y else g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- Wires with every NOT gate's value replaced by `y`. -/
def wiresY (C : Circuit) (x : List Bool) (y : Bool) : List Bool := C.gates.foldl (stepY y) x

/-- The overridden output `G x y`. -/
def evalY (C : Circuit) (x : List Bool) (y : Bool) : Bool := (wiresY C x y).getD C.output false

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_mono {l1 l2 : List Bool} (h : List.Forall₂ (· ≤ ·) l1 l2) (i : ℕ) :
    l1.getD i false ≤ l2.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hab
    | succ n => simpa only [List.getD_cons_succ] using ih n

theorem forall₂_map_getD {l1 l2 : List Bool} (h : List.Forall₂ (· ≤ ·) l1 l2) (is : List ℕ) :
    List.Forall₂ (· ≤ ·) (is.map fun i => l1.getD i false) (is.map fun i => l2.getD i false) := by
  induction is with
  | nil => simp
  | cons i is ih => exact List.Forall₂.cons (getD_mono h i) ih

theorem all_mono {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) : a.all id ≤ b.all id := by
  induction h with
  | nil => simp
  | @cons x y l1 l2 hab _ ih =>
    simp only [List.all_cons, id]
    cases x <;> cases y
    · simp
    · simp
    · exact absurd hab (by decide)
    · simpa using ih

theorem any_mono {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) : a.any id ≤ b.any id := by
  induction h with
  | nil => simp
  | @cons x y l1 l2 hab _ ih =>
    simp only [List.any_cons, id]
    cases x <;> cases y
    · simpa using ih
    · simp
    · exact absurd hab (by decide)
    · simp

theorem stepY_mono {w w' : List Bool} {y y' : Bool} (hw : List.Forall₂ (· ≤ ·) w w') (hy : y ≤ y')
    (g : Gate) (hg : AndOrNot g.op) :
    List.Forall₂ (· ≤ ·) (stepY y w g) (stepY y' w' g) := by
  unfold stepY
  refine List.rel_append hw (List.Forall₂.cons ?_ List.Forall₂.nil)
  have hm := forall₂_map_getD hw g.inputs
  rcases g with ⟨op, ins⟩
  cases op with
  | and => exact all_mono hm
  | or => exact any_mono hm
  | not => exact hy
  | mod m => exact hg.elim
  | maj => exact hg.elim

theorem foldl_stepY_mono (gs : List Gate) (hg : ∀ g ∈ gs, AndOrNot g.op) {w w' : List Bool}
    {y y' : Bool} (hw : List.Forall₂ (· ≤ ·) w w') (hy : y ≤ y') :
    List.Forall₂ (· ≤ ·) (gs.foldl (stepY y) w) (gs.foldl (stepY y') w') := by
  induction gs generalizing w w' with
  | nil => simpa using hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (stepY_mono hw hy g (hg g (List.mem_cons_self ..)))

theorem forall₂_refl (l : List Bool) : List.Forall₂ (· ≤ ·) l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons (le_refl a) ih

/-- `G x y` is monotone in both the inputs and the override bit. -/
theorem evalY_mono (C : Circuit) (hC : ∀ g ∈ C.gates, AndOrNot g.op) {x x' : List Bool}
    {y y' : Bool} (hx : List.Forall₂ (· ≤ ·) x x') (hy : y ≤ y') :
    evalY C x y ≤ evalY C x' y' :=
  getD_mono (foldl_stepY_mono C.gates hC hx hy) C.output

theorem foldl_noNot (gs : List Gate) (h : gs.countP (fun g => isNot g.op) = 0) (v : Bool)
    (w : List Bool) : gs.foldl step w = gs.foldl (stepY v) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.countP_cons] at h
    have hg : isNot g.op = false := by
      cases hn : isNot g.op <;> simp_all
    have hr : gs.countP (fun g => isNot g.op) = 0 := by omega
    simp only [List.foldl_cons]
    have : step w g = stepY v w g := by simp [step, stepY, hg]
    rw [this, ih hr]

theorem foldl_oneNot (gs : List Gate) (h : gs.countP (fun g => isNot g.op) ≤ 1) (w : List Bool) :
    ∃ v, gs.foldl step w = gs.foldl (stepY v) w := by
  induction gs generalizing w with
  | nil => exact ⟨false, rfl⟩
  | cons g gs ih =>
    rw [List.countP_cons] at h
    simp only [List.foldl_cons]
    cases hn : isNot g.op
    · obtain ⟨v, hv⟩ := ih (by simp_all) (step w g)
      exact ⟨v, by rw [hv]; simp [step, stepY, hn]⟩
    · refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false), ?_⟩
      have h0 : gs.countP (fun g => isNot g.op) = 0 := by simp only [hn, ↓reduceIte] at h; omega
      rw [foldl_noNot gs h0 (g.op.eval (g.inputs.map fun i => w.getD i false)) (step w g)]
      simp [step, stepY, hn]

/-- The single-NOT sandwich: the output equals `G x v` for some `v`, so it lies between
`G x false` and `G x true`, and `G` is monotone. -/
theorem sandwich (C : Circuit) (hC : ∀ g ∈ C.gates, AndOrNot g.op)
    (h1 : C.gates.countP (fun g => isNot g.op) ≤ 1) (x : List Bool) :
    (∃ v, C.eval x = evalY C x v) ∧ evalY C x false ≤ C.eval x ∧ C.eval x ≤ evalY C x true := by
  obtain ⟨v, hv⟩ := foldl_oneNot C.gates h1 x
  have he : C.eval x = evalY C x v := by
    simp only [Circuit.eval, wires_eq, evalY, wiresY, hv]
  refine ⟨⟨v, he⟩, ?_, ?_⟩ <;> rw [he] <;>
    exact evalY_mono C hC (forall₂_refl x) (by cases v <;> decide)

/-! ### The posted table -/

/-- The posted L-meta-16102 table, verbatim. -/
def table16102 : List Bool :=
  ([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1] : List ℕ).map (fun b => b == 1)

/-- The posted target function. -/
def f16102 : (Fin 6 → Bool) → Bool := PEqualNP.MetaComplexity.tableFun 6 table16102

def bv (b : Bool) : ℕ := if b then 1 else 0

theorem tableIndex_six (x : Fin 6 → Bool) :
    PEqualNP.MetaComplexity.tableIndex x =
      bv (x 0) + 2 * bv (x 1) + 4 * bv (x 2) + 8 * bv (x 3) + 16 * bv (x 4) + 32 * bv (x 5) := by
  simp only [PEqualNP.MetaComplexity.tableIndex, Fin.sum_univ_six, bv]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl

/-- The table on explicit bits. -/
def fb (a b c d e g : Bool) : Bool :=
  table16102.getD (bv a + 2 * bv b + 4 * bv c + 8 * bv d + 16 * bv e + 32 * bv g) false

theorem f16102_eq (x : Fin 6 → Bool) : f16102 x = fb (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  simp only [f16102, PEqualNP.MetaComplexity.tableFun, tableIndex_six, fb]

/-- Monotone in every input, on explicit bits (64 cases per coordinate). -/
theorem fb_mono :
    (∀ b c d e g : Bool, fb false b c d e g ≤ fb true b c d e g) ∧
    (∀ a c d e g : Bool, fb a false c d e g ≤ fb a true c d e g) ∧
    (∀ a b d e g : Bool, fb a b false d e g ≤ fb a b true d e g) ∧
    (∀ a b c e g : Bool, fb a b c false e g ≤ fb a b c true e g) ∧
    (∀ a b c d g : Bool, fb a b c d false g ≤ fb a b c d true g) ∧
    (∀ a b c d e : Bool, fb a b c d e false ≤ fb a b c d e true) := by
  decide

/-- The target is monotone: raising one input never lowers the value. -/
theorem f16102_mono (x : Fin 6 → Bool) (i : Fin 6) :
    f16102 (Function.update x i false) ≤ f16102 (Function.update x i true) := by
  rw [f16102_eq, f16102_eq]
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := fb_mono
  fin_cases i <;> simp [Function.update, m1, m2, m3, m4, m5, m6]

/-- Minimal positive certificates (masks 19, 21, 22, 24, 34, 36, 40) and maximal negative
certificates (masks 15, 18, 20, 49), bit `i` being input `i`. -/
theorem fb_certificates :
    fb true true false false true false = true ∧ fb true false true false true false = true ∧
    fb false true true false true false = true ∧ fb false false false true true false = true ∧
    fb false true false false false true = true ∧ fb false false true false false true = true ∧
    fb false false false true false true = true ∧
    fb true true true true false false = false ∧ fb false true false false true false = false ∧
    fb false false true false true false = false ∧ fb true false false false true true = false := by
  decide

end SatBridge.Meta16102
