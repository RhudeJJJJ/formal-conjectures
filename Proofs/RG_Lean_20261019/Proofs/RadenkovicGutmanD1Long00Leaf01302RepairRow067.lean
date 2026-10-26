/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01302RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01302_w_row067 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01302_w_affine)
theorem leaf01302_w_row067_weighted : leaf01302_w_row067=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01302_w_affine := by decide +kernel
theorem leaf01302_w_row067_identity : leaf01302_w_row067=NestedInteger.coefficientFrom 88 67 0 leaf01302_w_affine :=
  IntegerWeightedBernstein.checked 88 67 0 leaf01302_w_affine leaf01302_w_row067 IntegerBernsteinWeights88.row067 (IntegerBernsteinTable.checked (n := 2) 88 67 0 89 leaf01302_w_affine IntegerBernsteinWeights88.row067 leaf01302_w_affine_length IntegerBernsteinWeights88.row067_identity) leaf01302_w_row067_weighted
theorem leaf01302_w_row067_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01302_w_row067=true := by decide +kernel
#print axioms leaf01302_w_row067_weighted
#print axioms leaf01302_w_row067_identity
#print axioms leaf01302_w_row067_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
