/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01428RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01428_w_row049 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01428_w_affine)
theorem leaf01428_w_row049_weighted : leaf01428_w_row049=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01428_w_affine := by decide +kernel
theorem leaf01428_w_row049_identity : leaf01428_w_row049=NestedInteger.coefficientFrom 88 49 0 leaf01428_w_affine :=
  IntegerWeightedBernstein.checked 88 49 0 leaf01428_w_affine leaf01428_w_row049 IntegerBernsteinWeights88.row049 (IntegerBernsteinTable.checked (n := 2) 88 49 0 89 leaf01428_w_affine IntegerBernsteinWeights88.row049 leaf01428_w_affine_length IntegerBernsteinWeights88.row049_identity) leaf01428_w_row049_weighted
theorem leaf01428_w_row049_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01428_w_row049=true := by decide +kernel
#print axioms leaf01428_w_row049_weighted
#print axioms leaf01428_w_row049_identity
#print axioms leaf01428_w_row049_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
