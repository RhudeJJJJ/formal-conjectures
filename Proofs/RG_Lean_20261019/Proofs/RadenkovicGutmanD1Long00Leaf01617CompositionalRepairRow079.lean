/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01617CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01617_w_row079 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01617_w_affine)
theorem leaf01617_w_row079_weighted : leaf01617_w_row079=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01617_w_affine := by decide +kernel
theorem leaf01617_w_row079_identity : leaf01617_w_row079=NestedInteger.coefficientFrom 88 79 0 leaf01617_w_affine :=
  IntegerWeightedBernstein.checked 88 79 0 leaf01617_w_affine leaf01617_w_row079 IntegerBernsteinWeights88.row079 (IntegerBernsteinTable.checked (n := 2) 88 79 0 89 leaf01617_w_affine IntegerBernsteinWeights88.row079 leaf01617_w_affine_length IntegerBernsteinWeights88.row079_identity) leaf01617_w_row079_weighted
theorem leaf01617_w_row079_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01617_w_row079=true := by decide +kernel
#print axioms leaf01617_w_row079_weighted
#print axioms leaf01617_w_row079_identity
#print axioms leaf01617_w_row079_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
