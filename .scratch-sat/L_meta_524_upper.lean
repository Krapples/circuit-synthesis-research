import Mathlib
import PEqualNP.Defs

private def edgeCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [1, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [0, 9]⟩,
    ⟨.or, [1, 3]⟩, ⟨.and, [2, 11]⟩,
    ⟨.or, [3, 5]⟩, ⟨.and, [4, 13]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [10, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

set_option maxHeartbeats 1500000 in
theorem edgeCycleLeaf_upper :
    PEqualNP.MetaComplexity.HasCircuitSize 8
      (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 5) || (x 5 && x 6) || (x 0 && x 6) || (x 0 && x 7)) 11 := by
  refine ⟨edgeCircuit, ?_, by decide, ?_⟩
  · unfold PEqualNP.MetaComplexity.FanInTwo
    simp [edgeCircuit]
  · intro x
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, edgeCircuit, List.ofFn_succ,
      List.ofFn_zero, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.any_cons,
      List.all_nil, List.any_nil, id]
    change ((x 0 && (x 1 || x 6 || x 7)) || (x 2 && (x 1 || x 3))) ||
      ((x 4 && (x 3 || x 5)) || (x 5 && x 6)) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 5) || (x 5 && x 6) || (x 0 && x 6) || (x 0 && x 7))
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      cases h4 : x 4 <;> cases h5 : x 5 <;> cases h6 : x 6 <;> cases h7 : x 7 <;> rfl

