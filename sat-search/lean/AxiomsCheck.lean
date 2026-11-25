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
