/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01517_w_weights23 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 11 1 64 69 leaf01517_w_segment23)
theorem leaf01517_w_weights23_identity : leaf01517_w_weights23=IntegerWeightedOuter.weights 11 1 64 69 leaf01517_w_segment23 := by decide +kernel
noncomputable def leaf01517_w_piece23 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01517_w_weights23 leaf01517_w_segment23)
theorem leaf01517_w_piece23_weighted : leaf01517_w_piece23=IntegerWeightedOuter.applyWeights leaf01517_w_weights23 leaf01517_w_segment23 := by decide +kernel
theorem leaf01517_w_piece23_identity : leaf01517_w_piece23=IntegerOuterTerms.transform 11 1 64 69 leaf01517_w_segment23 :=
  IntegerWeightedOuter.checked 11 1 64 69 leaf01517_w_segment23 leaf01517_w_piece23 leaf01517_w_weights23 leaf01517_w_weights23_identity leaf01517_w_piece23_weighted
#print axioms leaf01517_w_weights23_identity
#print axioms leaf01517_w_piece23_weighted
#print axioms leaf01517_w_piece23_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
