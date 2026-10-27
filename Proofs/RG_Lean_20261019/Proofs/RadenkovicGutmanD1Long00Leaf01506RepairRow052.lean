/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01506RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01506_w_row052 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01506_w_affine)
theorem leaf01506_w_row052_weighted : leaf01506_w_row052=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01506_w_affine := by decide +kernel
theorem leaf01506_w_row052_identity : leaf01506_w_row052=NestedInteger.coefficientFrom 88 52 0 leaf01506_w_affine :=
  IntegerWeightedBernstein.checked 88 52 0 leaf01506_w_affine leaf01506_w_row052 IntegerBernsteinWeights88.row052 (IntegerBernsteinTable.checked (n := 2) 88 52 0 89 leaf01506_w_affine IntegerBernsteinWeights88.row052 leaf01506_w_affine_length IntegerBernsteinWeights88.row052_identity) leaf01506_w_row052_weighted
theorem leaf01506_w_row052_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01506_w_row052=true := by decide +kernel
#print axioms leaf01506_w_row052_weighted
#print axioms leaf01506_w_row052_identity
#print axioms leaf01506_w_row052_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
