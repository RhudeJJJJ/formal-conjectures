/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01277RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01277_w_row051 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01277_w_affine)
theorem leaf01277_w_row051_weighted : leaf01277_w_row051=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01277_w_affine := by decide +kernel
theorem leaf01277_w_row051_identity : leaf01277_w_row051=NestedInteger.coefficientFrom 88 51 0 leaf01277_w_affine :=
  IntegerWeightedBernstein.checked 88 51 0 leaf01277_w_affine leaf01277_w_row051 IntegerBernsteinWeights88.row051 (IntegerBernsteinTable.checked (n := 2) 88 51 0 89 leaf01277_w_affine IntegerBernsteinWeights88.row051 leaf01277_w_affine_length IntegerBernsteinWeights88.row051_identity) leaf01277_w_row051_weighted
theorem leaf01277_w_row051_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01277_w_row051=true := by decide +kernel
#print axioms leaf01277_w_row051_weighted
#print axioms leaf01277_w_row051_identity
#print axioms leaf01277_w_row051_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
