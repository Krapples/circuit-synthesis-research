import Expand7893

namespace Upper7893

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def base : Circuit :=
  ⟨[⟨.or,[2,6]⟩,⟨.and,[1,10]⟩,⟨.or,[1,4]⟩,⟨.or,[12,5]⟩,⟨.and,[0,13]⟩,
    ⟨.or,[2,4]⟩,⟨.or,[15,8]⟩,⟨.and,[3,16]⟩,⟨.or,[2,5]⟩,⟨.or,[18,9]⟩,
    ⟨.and,[7,19]⟩,⟨.or,[5,6]⟩,⟨.and,[8,21]⟩,⟨.or,[4,6]⟩,⟨.and,[9,23]⟩,
    ⟨.or,[14,17]⟩,⟨.or,[25,20]⟩,⟨.or,[26,22]⟩,⟨.or,[27,24]⟩],28⟩

abbrev edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(0,4),(3,4),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8),(4,9),(6,9),(7,9)]

def h (x : Fin 10 → Bool) : Bool :=
  (base.wires (List.ofFn (Function.update x 0 false))).getD 11 false

theorem gateCount : base.size = 19 := rfl

theorem legal : IsAO2 10 base := by decide +kernel

theorem safe : ∀ j g, 10 + j ≤ 11 → base.gates[j]? = some g → 0 ∉ g.inputs := by
  intro j g bound eq
  have small : j ≤ 1 := by omega
  interval_cases j <;> simp [base] at eq <;> subst g <;> decide

theorem guardOff : ∀ k ∈ ([50,104,116,138,208,276,402,548,554,770] : List ℕ),
    h (fun i => k.testBit i.val) = false := by decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 24000 in
theorem computes : ∀ x : Fin 10 → Bool,
    circuitFun 10 base (Function.update x 0 (x 0 || h x)) =
      edges.any (fun e => x e.1 && x e.2) := by decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 24000 in
theorem coverLower : ∀ t : Finset (Fin 10),
    edges.all (fun e => decide (e.1 ∈ t ∨ e.2 ∈ t)) = true → 6 ≤ t.card := by decide +kernel

theorem expandedWitness :
    ∃ C : Circuit, C.size = 20 ∧ IsAO2 10 C ∧
      (∃ p q : List Gate, C.gates = p ++ [⟨.or,[0,11]⟩] ++ q ∧
        ∀ g ∈ p ++ q, 0 ∉ g.inputs) ∧
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2) := by
  refine ⟨Expand7893.expand base 11, ?_, ?_, Expand7893.uniqueZeroReader base 11 safe, ?_⟩
  · rw [Expand7893.expandSize, gateCount]
  · apply Expand7893.expandLegal base 11 legal (by decide)
    rw [gateCount]
    decide
  · intro x
    have upper : 11 < 10 + base.size := by rw [gateCount]; decide
    exact (Expand7893.expandEval base 11 (by decide) upper safe x).trans (computes x)

end Upper7893

#print axioms Upper7893.computes
#print axioms Upper7893.coverLower
#print axioms Upper7893.expandedWitness
