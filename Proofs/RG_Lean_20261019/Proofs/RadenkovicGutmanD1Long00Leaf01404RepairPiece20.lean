/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01404RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01404_w_weights20 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 18 1 64 60 leaf01404_w_segment20)
theorem leaf01404_w_weights20_identity : leaf01404_w_weights20=IntegerWeightedOuter.weights 18 1 64 60 leaf01404_w_segment20 := by decide +kernel
noncomputable def leaf01404_w_piece20 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01404_w_weights20 leaf01404_w_segment20)
theorem leaf01404_w_piece20_weighted : leaf01404_w_piece20=IntegerWeightedOuter.applyWeights leaf01404_w_weights20 leaf01404_w_segment20 := by decide +kernel
theorem leaf01404_w_piece20_identity : leaf01404_w_piece20=IntegerOuterTerms.transform 18 1 64 60 leaf01404_w_segment20 :=
  IntegerWeightedOuter.checked 18 1 64 60 leaf01404_w_segment20 leaf01404_w_piece20 leaf01404_w_weights20 leaf01404_w_weights20_identity leaf01404_w_piece20_weighted
#print axioms leaf01404_w_weights20_identity
#print axioms leaf01404_w_piece20_weighted
#print axioms leaf01404_w_piece20_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
