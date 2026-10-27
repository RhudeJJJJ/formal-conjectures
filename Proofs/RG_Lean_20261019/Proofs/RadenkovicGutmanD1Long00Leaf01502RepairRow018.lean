/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01502RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01502_w_row018 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01502_w_affine)
theorem leaf01502_w_row018_weighted : leaf01502_w_row018=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01502_w_affine := by decide +kernel
theorem leaf01502_w_row018_identity : leaf01502_w_row018=NestedInteger.coefficientFrom 88 18 0 leaf01502_w_affine :=
  IntegerWeightedBernstein.checked 88 18 0 leaf01502_w_affine leaf01502_w_row018 IntegerBernsteinWeights88.row018 (IntegerBernsteinTable.checked (n := 2) 88 18 0 89 leaf01502_w_affine IntegerBernsteinWeights88.row018 leaf01502_w_affine_length IntegerBernsteinWeights88.row018_identity) leaf01502_w_row018_weighted
theorem leaf01502_w_row018_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01502_w_row018=true := by decide +kernel
#print axioms leaf01502_w_row018_weighted
#print axioms leaf01502_w_row018_identity
#print axioms leaf01502_w_row018_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
