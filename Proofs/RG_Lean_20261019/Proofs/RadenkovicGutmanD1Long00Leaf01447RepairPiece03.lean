/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01447RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01447_w_weights03 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 64 9 leaf01447_w_segment03)
theorem leaf01447_w_weights03_identity : leaf01447_w_weights03=IntegerWeightedOuter.weights 15 1 64 9 leaf01447_w_segment03 := by decide +kernel
noncomputable def leaf01447_w_piece03 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01447_w_weights03 leaf01447_w_segment03)
theorem leaf01447_w_piece03_weighted : leaf01447_w_piece03=IntegerWeightedOuter.applyWeights leaf01447_w_weights03 leaf01447_w_segment03 := by decide +kernel
theorem leaf01447_w_piece03_identity : leaf01447_w_piece03=IntegerOuterTerms.transform 15 1 64 9 leaf01447_w_segment03 :=
  IntegerWeightedOuter.checked 15 1 64 9 leaf01447_w_segment03 leaf01447_w_piece03 leaf01447_w_weights03 leaf01447_w_weights03_identity leaf01447_w_piece03_weighted
#print axioms leaf01447_w_weights03_identity
#print axioms leaf01447_w_piece03_weighted
#print axioms leaf01447_w_piece03_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
