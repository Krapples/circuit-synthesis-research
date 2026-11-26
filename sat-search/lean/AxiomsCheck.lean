-- Axiom audit for the formalized results (not part of the library).
-- Expected output for each: [propext, Classical.choice, Quot.sound].
import CircuitLemmas
open CircuitLemmas
#print axioms module_contraction
#print axioms peel_contraction
#print axioms module_sizeLE
#print axioms peel_sizeLE
#print axioms restrict_const
#print axioms minSize_perm
#print axioms Circuit.excess_identity
#print axioms CircuitLemmas.GateElim.bypass
#print axioms CircuitLemmas.GateElim.bypass_many
#print axioms CircuitLemmas.GateElim.realizes_restrict
#print axioms CircuitLemmas.GateElim.restrict_eliminates
#print axioms CircuitLemmas.GateElim.literal_extension
#print axioms CircuitLemmas.GateElim.delete_dead
#print axioms CircuitLemmas.GateElim.literal_extension_phase
#print axioms CircuitLemmas.GateElim.xnorConj_lower
#print axioms CircuitLemmas.GateElim.xnorConj_std_lower
#print axioms CircuitLemmas.GateElim.card_le_degCount
#print axioms CircuitLemmas.GateElim.excess_restriction
#print axioms CircuitLemmas.GateElim.xnorConj_restriction_lower
#print axioms CircuitLemmas.GateElim.three_step
#print axioms CircuitLemmas.GateElim.potential_lower
#print axioms CircuitLemmas.GateElim.potential_restriction_lower
#print axioms CircuitLemmas.GateElim.block_product_lower
#print axioms CircuitLemmas.GateElim.block_restriction_lower
