/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01497RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01497_w_row081 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01497_w_affine)
theorem leaf01497_w_row081_weighted : leaf01497_w_row081=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01497_w_affine := by decide +kernel
theorem leaf01497_w_row081_identity : leaf01497_w_row081=NestedInteger.coefficientFrom 88 81 0 leaf01497_w_affine :=
  IntegerWeightedBernstein.checked 88 81 0 leaf01497_w_affine leaf01497_w_row081 IntegerBernsteinWeights88.row081 (IntegerBernsteinTable.checked (n := 2) 88 81 0 89 leaf01497_w_affine IntegerBernsteinWeights88.row081 leaf01497_w_affine_length IntegerBernsteinWeights88.row081_identity) leaf01497_w_row081_weighted
theorem leaf01497_w_row081_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01497_w_row081=true := by decide +kernel
#print axioms leaf01497_w_row081_weighted
#print axioms leaf01497_w_row081_identity
#print axioms leaf01497_w_row081_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
