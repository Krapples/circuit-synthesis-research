import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

namespace ResearchVerification

/-- Smoke test using the actual L-meta-3754 definitions, not a proof of
    the one-junk or many-junk case. -/
theorem zeroJunkClean (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (h0 : junk G C = ∅)
    (k : ℕ) (hk : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) : BelowF G C k := by
  have hmem : k ∈ junk G C ↔ IsDirtyAnd n G C k := by
    simp [junk, gatesWhere, Finset.mem_filter, Finset.mem_range, hk]
  have hn : ¬ IsDirtyAnd n G C k := by
    intro hd
    exact Finset.notMem_empty k (h0 ▸ hmem.mpr hd)
  have hnd : ¬ IsDirty n G C k := fun hd => hn ⟨hand, hd⟩
  intro x hx
  cases hFx : graphFun G ∅ x with
  | true => rfl
  | false => exact (hnd ⟨hk, x, hx, hFx⟩).elim

#print axioms zeroJunkClean

end ResearchVerification
