/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01502RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01502_w_row080 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01502_w_affine)
theorem leaf01502_w_row080_weighted : leaf01502_w_row080=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01502_w_affine := by decide +kernel
theorem leaf01502_w_row080_identity : leaf01502_w_row080=NestedInteger.coefficientFrom 88 80 0 leaf01502_w_affine :=
  IntegerWeightedBernstein.checked 88 80 0 leaf01502_w_affine leaf01502_w_row080 IntegerBernsteinWeights88.row080 (IntegerBernsteinTable.checked (n := 2) 88 80 0 89 leaf01502_w_affine IntegerBernsteinWeights88.row080 leaf01502_w_affine_length IntegerBernsteinWeights88.row080_identity) leaf01502_w_row080_weighted
theorem leaf01502_w_row080_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01502_w_row080=true := by decide +kernel
#print axioms leaf01502_w_row080_weighted
#print axioms leaf01502_w_row080_identity
#print axioms leaf01502_w_row080_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
