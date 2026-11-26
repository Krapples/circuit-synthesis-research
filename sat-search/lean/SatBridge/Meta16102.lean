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
import SatBridge.Transfer

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

/-! ### Binary-gate transfer and the reduction to the core -/

/-- A proper binary AND or OR gate (exactly two inputs). -/
def isBin (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [_, _] => true
  | GateOp.or, [_, _] => true
  | _, _ => false

theorem tstep_len (n : ℕ)
    (st : List CircuitLemmas.GateElim.Gate × List CircuitLemmas.GateElim.Ref) (g : Gate) :
    (SatBridge.step n st g).1.length = st.1.length + (if isBin g then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩ <;> simp [SatBridge.step, isBin]

theorem tfoldl_len (n : ℕ) : ∀ (gs : List Gate)
    (st : List CircuitLemmas.GateElim.Gate × List CircuitLemmas.GateElim.Ref),
    (gs.foldl (SatBridge.step n) st).1.length = st.1.length + gs.countP isBin
  | [], st => by simp
  | g :: gs, st => by
    rw [List.foldl_cons, tfoldl_len n gs, tstep_len, List.countP_cons]
    split <;> omega

/-- The transfer, counting only proper binary gates: NOT, unary and nullary gates are free. -/
theorem transfer_binary (n : ℕ) (C : Circuit) (hC : ∀ g ∈ C.gates, SatBridge.Ok g) :
    CircuitLemmas.GateElim.Realizes n (fun x => C.eval (List.ofFn fun i : Fin n => x i))
      (C.gates.countP isBin) := by
  refine ⟨SatBridge.translate n C, rfl, ?_, ?_⟩
  · simp [SatBridge.translate, CircuitLemmas.GateElim.Circuit.size, tfoldl_len]
  · intro x
    have := (SatBridge.inv_foldl C.gates _ _ hC (SatBridge.inv_init n x)).1.2.2 C.output
    simpa [SatBridge.translate, CircuitLemmas.GateElim.Circuit.eval, Circuit.eval,
      Circuit.wires] using this

theorem countP_split {α : Type} (l : List α) (p r : α → Bool) :
    l.countP p = l.countP (fun h => p h && r h) + l.countP (fun h => p h && !r h) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    cases p a <;> cases r a <;> simp <;> omega

theorem countP_compl {α : Type} (l : List α) (r : α → Bool) :
    l.countP r + l.countP (fun h => !r h) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.length_cons]
    cases r a <;> simp <;> omega

/-- The posted L-meta-16102 statement, verbatim up to naming the table. -/
def Posted : Prop :=
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C ∧ C.size ≤ 9 ∧
    (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.tableFun 6 table16102 x) ∧
    (∀ j < C.size, C.output = 6 + j ∨ ∃ i < C.size, j < i ∧
      6 + j ∈ (C.gates.getD i ⟨GateOp.and, []⟩).inputs) ∧
    (∀ g ∈ C.gates, g.op = GateOp.not → 6 ≤ g.inputs.headD 0 →
      (C.gates.getD (g.inputs.headD 0 - 6) ⟨GateOp.and, []⟩).op ≠ GateOp.not) ∧
    (∃ g ∈ C.gates, g.op = GateOp.not ∧ 6 ≤ g.inputs.headD 0)

/-- The target as a function of `ℕ`-indexed inputs, for the AIG model. -/
def F (x : ℕ → Bool) : Bool := f16102 (fun i : Fin 6 => x i)

/-- **Reduction.** If the target has no free-NOT AIG with 7 gates, every posted candidate has exactly
nine gates: eight proper binary AND/OR gates and one NOT. In particular it is an AND/OR/NOT circuit
with one NOT, so `sandwich` applies. The hypothesis `hA` is the eight-binary-gate lower bound, which is
checked here only on paper. -/
theorem posted_core (hA : ¬ CircuitLemmas.GateElim.Realizes 6 F 7) (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 9)
    (heval : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f16102 x)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not ∧ 6 ≤ g.inputs.headD 0) :
    C.size = 9 ∧ C.gates.countP isBin = 8 ∧ C.gates.countP (fun g => isNot g.op) = 1 ∧
      (∀ g ∈ C.gates, AndOrNot g.op) := by
  have hR := transfer_binary 6 C (fun g hg => hfan g hg)
  have h8 : 8 ≤ C.gates.countP isBin := by
    by_contra hlt
    obtain ⟨D, hD, hDs, hDf⟩ := hR
    exact hA ⟨D, hD, by omega, fun x => by rw [hDf]; exact heval (fun i => x i)⟩
  obtain ⟨g, hg, hgnot, -⟩ := hnot
  have hgb : isBin g = false := by rcases g with ⟨op, ins⟩; simp only at hgnot; subst hgnot; rfl
  have hsplit := countP_compl C.gates isBin
  have hsplit2 := countP_split C.gates (fun h => !isBin h) (fun h => isNot h.op)
  have hpos : 0 < C.gates.countP (fun h => !isBin h && isNot h.op) :=
    List.countP_pos_iff.2 ⟨g, hg, by simp [hgb, hgnot, isNot]⟩
  have hsz : C.size = C.gates.length := rfl
  have hrest : C.gates.countP (fun h => !isBin h && !isNot h.op) = 0 := by omega
  have hnb : C.gates.countP (fun h => !isBin h) = 1 := by omega
  have hnotle : C.gates.countP (fun h => isNot h.op) ≤ 1 := by
    rw [← hnb]
    refine List.countP_mono_left fun h _ hh => ?_
    rcases h with ⟨op, ins⟩; cases op <;> simp_all [isNot, isBin]
  refine ⟨by omega, by omega, le_antisymm hnotle ?_, ?_⟩
  · exact List.countP_pos_iff.2 ⟨g, hg, by simp [hgnot, isNot]⟩
  · intro h hh
    have h0 := (List.countP_eq_zero.1 hrest) h hh
    rcases h with ⟨op, ins⟩
    cases op <;> simp_all [AndOrNot, isNot, isBin]

end SatBridge.Meta16102
