/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01408RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01408_w_row070 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01408_w_affine)
theorem leaf01408_w_row070_weighted : leaf01408_w_row070=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01408_w_affine := by decide +kernel
theorem leaf01408_w_row070_identity : leaf01408_w_row070=NestedInteger.coefficientFrom 88 70 0 leaf01408_w_affine :=
  IntegerWeightedBernstein.checked 88 70 0 leaf01408_w_affine leaf01408_w_row070 IntegerBernsteinWeights88.row070 (IntegerBernsteinTable.checked (n := 2) 88 70 0 89 leaf01408_w_affine IntegerBernsteinWeights88.row070 leaf01408_w_affine_length IntegerBernsteinWeights88.row070_identity) leaf01408_w_row070_weighted
theorem leaf01408_w_row070_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01408_w_row070=true := by decide +kernel
#print axioms leaf01408_w_row070_weighted
#print axioms leaf01408_w_row070_identity
#print axioms leaf01408_w_row070_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
