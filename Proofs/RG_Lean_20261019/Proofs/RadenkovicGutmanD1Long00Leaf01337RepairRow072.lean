/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01337RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01337_w_row072 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01337_w_affine)
theorem leaf01337_w_row072_weighted : leaf01337_w_row072=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01337_w_affine := by decide +kernel
theorem leaf01337_w_row072_identity : leaf01337_w_row072=NestedInteger.coefficientFrom 88 72 0 leaf01337_w_affine :=
  IntegerWeightedBernstein.checked 88 72 0 leaf01337_w_affine leaf01337_w_row072 IntegerBernsteinWeights88.row072 (IntegerBernsteinTable.checked (n := 2) 88 72 0 89 leaf01337_w_affine IntegerBernsteinWeights88.row072 leaf01337_w_affine_length IntegerBernsteinWeights88.row072_identity) leaf01337_w_row072_weighted
theorem leaf01337_w_row072_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01337_w_row072=true := by decide +kernel
#print axioms leaf01337_w_row072_weighted
#print axioms leaf01337_w_row072_identity
#print axioms leaf01337_w_row072_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
