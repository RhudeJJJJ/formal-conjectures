/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01347RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01347_w_row028 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01347_w_affine)
theorem leaf01347_w_row028_weighted : leaf01347_w_row028=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01347_w_affine := by decide +kernel
theorem leaf01347_w_row028_identity : leaf01347_w_row028=NestedInteger.coefficientFrom 88 28 0 leaf01347_w_affine :=
  IntegerWeightedBernstein.checked 88 28 0 leaf01347_w_affine leaf01347_w_row028 IntegerBernsteinWeights88.row028 (IntegerBernsteinTable.checked (n := 2) 88 28 0 89 leaf01347_w_affine IntegerBernsteinWeights88.row028 leaf01347_w_affine_length IntegerBernsteinWeights88.row028_identity) leaf01347_w_row028_weighted
theorem leaf01347_w_row028_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01347_w_row028=true := by decide +kernel
#print axioms leaf01347_w_row028_weighted
#print axioms leaf01347_w_row028_identity
#print axioms leaf01347_w_row028_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
