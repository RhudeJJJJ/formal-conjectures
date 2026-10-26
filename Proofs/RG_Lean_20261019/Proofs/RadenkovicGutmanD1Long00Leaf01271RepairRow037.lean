/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01271RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01271_w_row037 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01271_w_affine)
theorem leaf01271_w_row037_weighted : leaf01271_w_row037=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01271_w_affine := by decide +kernel
theorem leaf01271_w_row037_identity : leaf01271_w_row037=NestedInteger.coefficientFrom 88 37 0 leaf01271_w_affine :=
  IntegerWeightedBernstein.checked 88 37 0 leaf01271_w_affine leaf01271_w_row037 IntegerBernsteinWeights88.row037 (IntegerBernsteinTable.checked (n := 2) 88 37 0 89 leaf01271_w_affine IntegerBernsteinWeights88.row037 leaf01271_w_affine_length IntegerBernsteinWeights88.row037_identity) leaf01271_w_row037_weighted
theorem leaf01271_w_row037_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01271_w_row037=true := by decide +kernel
#print axioms leaf01271_w_row037_weighted
#print axioms leaf01271_w_row037_identity
#print axioms leaf01271_w_row037_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
