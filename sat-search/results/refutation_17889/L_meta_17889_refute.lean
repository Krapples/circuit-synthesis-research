import Mathlib
import PEqualNP.Defs

/-! Refutation of the posted statement of desk step L-meta-17889 (no 4-cycle-free hypothesis):
with `x1 = x2 = 2`, `E = K_{2,2}` and `C0 = (p0 ∨ p1) ∧ (l0 ∨ l1)` (3 gates), erasing the edge
`(0,0)` leaves the path `p0 l1 ∨ p1 l0 ∨ p1 l1`, which no `IsAO2` circuit with at most 2 gates
computes. -/

namespace K22Refute
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def C0 : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩

theorem C0_ao : PEqualNP.TopForm.IsAO2 (2 + 2) C0 := by decide

theorem C0_fun : ∀ (x9 : Fin (2 + 2) → Bool), circuitFun (2 + 2) C0 x9 =
    Decidable.decide (∃ (x10 : Fin 2) (x11 : Fin 2), (x10, x11) ∈ (Finset.univ : Finset (Fin 2 × Fin 2)) ∧
      x9 (Fin.castAdd 2 x10) = Bool.true ∧ x9 (Fin.natAdd 2 x11) = Bool.true) := by decide

def opOf (b : Bool) : GateOp := if b then GateOp.and else GateOp.or

def mk0 (o : Fin 5) : Circuit := ⟨[], o.val⟩
def mk1 (op0 : Bool) (a b : Fin 4) (o : Fin 6) : Circuit := ⟨[⟨opOf op0, [a.val, b.val]⟩], o.val⟩
def mk2 (op0 op1 : Bool) (a b : Fin 4) (c d : Fin 5) (o : Fin 7) : Circuit :=
  ⟨[⟨opOf op0, [a.val, b.val]⟩, ⟨opOf op1, [c.val, d.val]⟩], o.val⟩

/-- Five test inputs (order `p0 p1 l0 l1`): consecutive pairs differ in one variable each, and
`fp` changes along each of the four single-variable flips. -/
def T : List (Fin 4 → Bool) := [![false, false, false, true], ![true, false, false, true],
  ![false, true, false, true], ![false, true, false, false], ![false, true, true, false]]

def fp (x : Fin 4 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3)

def ok (C : Circuit) : Bool := T.all fun x => circuitFun 4 C x == fp x

theorem no0 : ∀ o : Fin 5, ok (mk0 o) = false := by decide
theorem no1 : ∀ op0 : Bool, ∀ a b : Fin 4, ∀ o : Fin 6, ok (mk1 op0 a b o) = false := by decide
set_option maxRecDepth 100000 in
theorem no2 : ∀ op0 op1 : Bool, ∀ a b : Fin 4, ∀ c d : Fin 5, ∀ o : Fin 7,
    ok (mk2 op0 op1 a b c d o) = false := by decide


theorem wires_length (gs : List Gate) (o : ℕ) : ∀ x : List Bool,
    (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp [Circuit.wires]
  | cons g gs ih =>
    intro x
    have := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    simp only [Circuit.wires, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem eval_clip (C : Circuit) (x : List Bool) :
    C.eval x = (⟨C.gates, min C.output (x.length + C.gates.length)⟩ : Circuit).eval x := by
  obtain ⟨gs, o⟩ := C
  have hl := wires_length gs o x
  have hw : Circuit.wires ⟨gs, min o (x.length + gs.length)⟩ x = Circuit.wires ⟨gs, o⟩ x := rfl
  unfold Circuit.eval
  rw [hw]
  by_cases h : o ≤ x.length + gs.length
  · simp [min_eq_left h]
  · rw [List.getD_eq_default _ _ (by simp only at hl ⊢; omega),
      List.getD_eq_default _ _ (by simp only at hl ⊢; omega)]

theorem ok_clip (C : Circuit) : ok C = ok ⟨C.gates, min C.output (4 + C.gates.length)⟩ := by
  unfold ok circuitFun
  congr 1; funext x
  rw [eval_clip C (List.ofFn x), List.length_ofFn]

theorem gate_form (g : Gate) (h1 : g.op = GateOp.and ∨ g.op = GateOp.or) (h2 : g.inputs.length = 2) :
    ∃ (b : Bool) (i j : ℕ), g = ⟨opOf b, [i, j]⟩ := by
  obtain ⟨op, ins⟩ := g
  match ins, h2 with
  | [i, j], _ =>
    rcases h1 with h | h
    · exact ⟨true, i, j, by simp only at h; subst h; rfl⟩
    · exact ⟨false, i, j, by simp only at h; subst h; rfl⟩

theorem small (C : Circuit) (hs : C.gates.length < 3) (hA : PEqualNP.TopForm.IsAO2 4 C)
    (hT : ok C = true) : False := by
  rw [ok_clip] at hT
  obtain ⟨hAO, hRB, hL⟩ := hA
  obtain ⟨gs, o⟩ := C
  simp only at hs hT hAO hRB hL
  match gs, hs, hT, hAO, hRB, hL with
  | [], _, hT, _, _, _ =>
    have := no0 ⟨min o 4, by omega⟩
    exact absurd hT (by rw [show (⟨[], min o (4 + [].length)⟩ : Circuit) = mk0 ⟨min o 4, by omega⟩ from rfl, this]; simp)
  | [g0], _, hT, hAO, hRB, hL =>
    obtain ⟨b0, i, j, rfl⟩ := gate_form g0 (hAO g0 (by simp)) (hL g0 (by simp))
    have hi : i < 4 := hRB 0 (by simp) i (by simp [gateAt])
    have hj : j < 4 := hRB 0 (by simp) j (by simp [gateAt])
    have := no1 b0 ⟨i, hi⟩ ⟨j, hj⟩ ⟨min o 5, by omega⟩
    have h2 : ok (mk1 b0 ⟨i, hi⟩ ⟨j, hj⟩ ⟨min o 5, by omega⟩) = true := hT
    rw [this] at h2; exact absurd h2 (by simp)
  | [g0, g1], _, hT, hAO, hRB, hL =>
    obtain ⟨b0, i, j, rfl⟩ := gate_form g0 (hAO g0 (by simp)) (hL g0 (by simp))
    obtain ⟨b1, c, d, rfl⟩ := gate_form g1 (hAO g1 (by simp)) (hL g1 (by simp))
    have hi : i < 4 := hRB 0 (by simp) i (by simp [gateAt])
    have hj : j < 4 := hRB 0 (by simp) j (by simp [gateAt])
    have hc : c < 5 := hRB 1 (by simp) c (by simp [gateAt])
    have hd : d < 5 := hRB 1 (by simp) d (by simp [gateAt])
    have := no2 b0 b1 ⟨i, hi⟩ ⟨j, hj⟩ ⟨c, hc⟩ ⟨d, hd⟩ ⟨min o 6, by omega⟩
    have h2 : ok (mk2 b0 b1 ⟨i, hi⟩ ⟨j, hj⟩ ⟨c, hc⟩ ⟨d, hd⟩ ⟨min o 6, by omega⟩) = true := hT
    rw [this] at h2; exact absurd h2 (by simp)
  | _ :: _ :: _ :: _, hs, _, _, _, _ => simp at hs; omega

theorem T_spec : ∀ x ∈ T, Decidable.decide (∃ (x12 : Fin 2) (x13 : Fin 2),
    (x12, x13) ∈ (Finset.univ : Finset (Fin 2 × Fin 2)).erase (0, 0) ∧
    x (Fin.castAdd 2 x12) = Bool.true ∧ x (Fin.natAdd 2 x13) = Bool.true) = fp x := by decide

end K22Refute

open K22Refute in
theorem not_L_meta_17889 : ¬ (∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Fin x1 × Fin x2) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4 ∈ x3 → (fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) x3 x5 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size < x5.size ∧ (fun (x9 : Finset (Fin x1 × Fin x2)) (x10 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x10 ∧ ∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x10 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x9 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) (x3.erase x4) x8) := by
  intro h
  obtain ⟨C', hsz, hA, hf⟩ := h 2 2 Finset.univ (0, 0) C0 (Finset.mem_univ _) ⟨C0_ao, C0_fun⟩
  have hs : C'.gates.length < 3 := hsz
  apply small C' hs hA
  unfold ok
  rw [List.all_eq_true]
  intro x hx
  rw [beq_iff_eq, ← T_spec x hx]
  exact hf x

#print axioms not_L_meta_17889
