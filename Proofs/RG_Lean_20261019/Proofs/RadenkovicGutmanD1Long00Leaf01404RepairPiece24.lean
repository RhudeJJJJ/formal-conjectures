/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01404RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01404_w_weights24 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 18 1 64 72 leaf01404_w_segment24)
theorem leaf01404_w_weights24_identity : leaf01404_w_weights24=IntegerWeightedOuter.weights 18 1 64 72 leaf01404_w_segment24 := by decide +kernel
noncomputable def leaf01404_w_piece24 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01404_w_weights24 leaf01404_w_segment24)
theorem leaf01404_w_piece24_weighted : leaf01404_w_piece24=IntegerWeightedOuter.applyWeights leaf01404_w_weights24 leaf01404_w_segment24 := by decide +kernel
theorem leaf01404_w_piece24_identity : leaf01404_w_piece24=IntegerOuterTerms.transform 18 1 64 72 leaf01404_w_segment24 :=
  IntegerWeightedOuter.checked 18 1 64 72 leaf01404_w_segment24 leaf01404_w_piece24 leaf01404_w_weights24 leaf01404_w_weights24_identity leaf01404_w_piece24_weighted
#print axioms leaf01404_w_weights24_identity
#print axioms leaf01404_w_piece24_weighted
#print axioms leaf01404_w_piece24_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
