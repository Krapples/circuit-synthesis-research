import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_clb_120

/-! Refutations of the desk statements L-clb-123 and L-clb-124 from the checked floor L-clb-120
(window w = 1, admissible H = 4 = J). The negated propositions below are the posted statements verbatim. -/

theorem not_L_clb_123 : ¬ (
  let n := 3
  let w := 1
  let P := 2^(w+1)
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.succ_pos 2)⟩ : Fin n)
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ raw : Fin (n*P) → Bool,
      let entries := List.ofFn raw
      let pass := fun (x : Fin n → Bool) => ∀ i : Fin n,
        let word := ∑ j : Fin (w+1), if x (loc (i.val+j.val)) then 2^j.val else 0
        entries.getD (i.val*P+word) false = true
      C.eval entries = (((Finset.univ : Finset (Fin n → Bool)).filter pass).card).testBit 0
  ∃ C, fits C ∧ binary C ≤ 16) := by
  intro hex
  obtain ⟨C, hfit, hb⟩ := hex
  have h := ((PEqualNP.Outside.L_clb_120 3 1 (by norm_num)).1 4 (by norm_num) (Or.inl (by decide)) C hfit).1
  have h2 : 17 ≤ C.size - (C.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length := h
  have hb' : C.size - (C.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ≤ 16 := hb
  omega

theorem not_L_clb_124 : ¬ (
  let n := 4
  let w := 1
  let P := 2^(w+1)
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.succ_pos 3)⟩ : Fin n)
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ raw : Fin (n*P) → Bool,
      let entries := List.ofFn raw
      let pass := fun (x : Fin n → Bool) => ∀ i : Fin n,
        let word := ∑ j : Fin (w+1), if x (loc (i.val+j.val)) then 2^j.val else 0
        entries.getD (i.val*P+word) false = true
      C.eval entries = (((Finset.univ : Finset (Fin n → Bool)).filter pass).card).testBit 0
  ∃ C, fits C ∧ binary C ≤ 20) := by
  intro hex
  obtain ⟨C, hfit, hb⟩ := hex
  have h := ((PEqualNP.Outside.L_clb_120 4 1 (by norm_num)).1 4 (by norm_num) (Or.inl (by decide)) C hfit).1
  have h2 : 21 ≤ C.size - (C.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length := h
  have hb' : C.size - (C.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ≤ 20 := hb
  omega

#print axioms not_L_clb_123
#print axioms not_L_clb_124
