import Mathlib
import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds

def localWitness : Circuit := ⟨[⟨.or, [10, 11]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [2, 18]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [3, 20]⟩, ⟨.and, [21, 15]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [23, 24]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 26]⟩, ⟨.and, [27, 12]⟩, ⟨.or, [16, 12]⟩, ⟨.and, [6, 29]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [26, 7]⟩, ⟨.and, [34, 14]⟩, ⟨.or, [20, 6]⟩, ⟨.or, [36, 7]⟩, ⟨.and, [37, 13]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [39, 25]⟩, ⟨.or, [40, 28]⟩, ⟨.or, [41, 30]⟩, ⟨.or, [42, 33]⟩, ⟨.or, [43, 35]⟩, ⟨.or, [44, 38]⟩], 45⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem localRepUpper : PEqualNP.Represents.RepSizeAtMost
    (fun u v : Fin 8 => (7583035862004050432 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨localWitness, ?_, by decide +kernel, by decide +kernel⟩
  intro gate member
  simp only [localWitness, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

#print axioms localRepUpper