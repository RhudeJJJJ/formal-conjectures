/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01404RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01404_w_row025 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01404_w_affine)
theorem leaf01404_w_row025_weighted : leaf01404_w_row025=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01404_w_affine := by decide +kernel
theorem leaf01404_w_row025_identity : leaf01404_w_row025=NestedInteger.coefficientFrom 88 25 0 leaf01404_w_affine :=
  IntegerWeightedBernstein.checked 88 25 0 leaf01404_w_affine leaf01404_w_row025 IntegerBernsteinWeights88.row025 (IntegerBernsteinTable.checked (n := 2) 88 25 0 89 leaf01404_w_affine IntegerBernsteinWeights88.row025 leaf01404_w_affine_length IntegerBernsteinWeights88.row025_identity) leaf01404_w_row025_weighted
theorem leaf01404_w_row025_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01404_w_row025=true := by decide +kernel
#print axioms leaf01404_w_row025_weighted
#print axioms leaf01404_w_row025_identity
#print axioms leaf01404_w_row025_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
