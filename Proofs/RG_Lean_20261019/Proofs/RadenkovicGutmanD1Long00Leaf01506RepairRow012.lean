/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01506RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01506_w_row012 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01506_w_affine)
theorem leaf01506_w_row012_weighted : leaf01506_w_row012=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01506_w_affine := by decide +kernel
theorem leaf01506_w_row012_identity : leaf01506_w_row012=NestedInteger.coefficientFrom 88 12 0 leaf01506_w_affine :=
  IntegerWeightedBernstein.checked 88 12 0 leaf01506_w_affine leaf01506_w_row012 IntegerBernsteinWeights88.row012 (IntegerBernsteinTable.checked (n := 2) 88 12 0 89 leaf01506_w_affine IntegerBernsteinWeights88.row012 leaf01506_w_affine_length IntegerBernsteinWeights88.row012_identity) leaf01506_w_row012_weighted
theorem leaf01506_w_row012_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01506_w_row012=true := by decide +kernel
#print axioms leaf01506_w_row012_weighted
#print axioms leaf01506_w_row012_identity
#print axioms leaf01506_w_row012_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
