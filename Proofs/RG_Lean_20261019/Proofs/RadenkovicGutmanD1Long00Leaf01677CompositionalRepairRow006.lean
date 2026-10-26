/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01677CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01677_w_row006 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01677_w_affine)
theorem leaf01677_w_row006_weighted : leaf01677_w_row006=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01677_w_affine := by decide +kernel
theorem leaf01677_w_row006_identity : leaf01677_w_row006=NestedInteger.coefficientFrom 88 6 0 leaf01677_w_affine :=
  IntegerWeightedBernstein.checked 88 6 0 leaf01677_w_affine leaf01677_w_row006 IntegerBernsteinWeights88.row006 (IntegerBernsteinTable.checked (n := 2) 88 6 0 89 leaf01677_w_affine IntegerBernsteinWeights88.row006 leaf01677_w_affine_length IntegerBernsteinWeights88.row006_identity) leaf01677_w_row006_weighted
theorem leaf01677_w_row006_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01677_w_row006=true := by decide +kernel
#print axioms leaf01677_w_row006_weighted
#print axioms leaf01677_w_row006_identity
#print axioms leaf01677_w_row006_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
