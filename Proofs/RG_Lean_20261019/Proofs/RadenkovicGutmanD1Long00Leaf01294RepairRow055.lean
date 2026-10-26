/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01294RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01294_w_row055 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01294_w_affine)
theorem leaf01294_w_row055_weighted : leaf01294_w_row055=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01294_w_affine := by decide +kernel
theorem leaf01294_w_row055_identity : leaf01294_w_row055=NestedInteger.coefficientFrom 88 55 0 leaf01294_w_affine :=
  IntegerWeightedBernstein.checked 88 55 0 leaf01294_w_affine leaf01294_w_row055 IntegerBernsteinWeights88.row055 (IntegerBernsteinTable.checked (n := 2) 88 55 0 89 leaf01294_w_affine IntegerBernsteinWeights88.row055 leaf01294_w_affine_length IntegerBernsteinWeights88.row055_identity) leaf01294_w_row055_weighted
theorem leaf01294_w_row055_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01294_w_row055=true := by decide +kernel
#print axioms leaf01294_w_row055_weighted
#print axioms leaf01294_w_row055_identity
#print axioms leaf01294_w_row055_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
