/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01404RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01404_w_weights11 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 18 1 64 33 leaf01404_w_segment11)
theorem leaf01404_w_weights11_identity : leaf01404_w_weights11=IntegerWeightedOuter.weights 18 1 64 33 leaf01404_w_segment11 := by decide +kernel
noncomputable def leaf01404_w_piece11 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01404_w_weights11 leaf01404_w_segment11)
theorem leaf01404_w_piece11_weighted : leaf01404_w_piece11=IntegerWeightedOuter.applyWeights leaf01404_w_weights11 leaf01404_w_segment11 := by decide +kernel
theorem leaf01404_w_piece11_identity : leaf01404_w_piece11=IntegerOuterTerms.transform 18 1 64 33 leaf01404_w_segment11 :=
  IntegerWeightedOuter.checked 18 1 64 33 leaf01404_w_segment11 leaf01404_w_piece11 leaf01404_w_weights11 leaf01404_w_weights11_identity leaf01404_w_piece11_weighted
#print axioms leaf01404_w_weights11_identity
#print axioms leaf01404_w_piece11_weighted
#print axioms leaf01404_w_piece11_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
