/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01602CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01602_w_weights24 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 128 72 leaf01602_w_segment24)
theorem leaf01602_w_weights24_identity : leaf01602_w_weights24=IntegerWeightedOuter.weights 16 1 128 72 leaf01602_w_segment24 := by decide +kernel
noncomputable def leaf01602_w_piece24 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01602_w_weights24 leaf01602_w_segment24)
theorem leaf01602_w_piece24_weighted : leaf01602_w_piece24=IntegerWeightedOuter.applyWeights leaf01602_w_weights24 leaf01602_w_segment24 := by decide +kernel
theorem leaf01602_w_piece24_identity : leaf01602_w_piece24=IntegerOuterTerms.transform 16 1 128 72 leaf01602_w_segment24 :=
  IntegerWeightedOuter.checked 16 1 128 72 leaf01602_w_segment24 leaf01602_w_piece24 leaf01602_w_weights24 leaf01602_w_weights24_identity leaf01602_w_piece24_weighted
#print axioms leaf01602_w_weights24_identity
#print axioms leaf01602_w_piece24_weighted
#print axioms leaf01602_w_piece24_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
