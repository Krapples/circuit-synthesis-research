import Mathlib
import PEqualNP.Defs

namespace LMeta16102Audit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1,2]⟩, ⟨.or, [3,6]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩,
    ⟨.or, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [5,11]⟩, ⟨.and, [7,12]⟩], 13⟩

def bits : List Bool := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).map (fun b => b == 1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem monotoneUpper : PEqualNP.MetaComplexity.Monotone2 witness ∧ witness.size = 8 ∧
    ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = tableFun 6 bits x := by
  refine ⟨?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

#print axioms monotoneUpper
end LMeta16102Audit
