/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01442RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01442_w_row015 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01442_w_affine)
theorem leaf01442_w_row015_weighted : leaf01442_w_row015=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01442_w_affine := by decide +kernel
theorem leaf01442_w_row015_identity : leaf01442_w_row015=NestedInteger.coefficientFrom 88 15 0 leaf01442_w_affine :=
  IntegerWeightedBernstein.checked 88 15 0 leaf01442_w_affine leaf01442_w_row015 IntegerBernsteinWeights88.row015 (IntegerBernsteinTable.checked (n := 2) 88 15 0 89 leaf01442_w_affine IntegerBernsteinWeights88.row015 leaf01442_w_affine_length IntegerBernsteinWeights88.row015_identity) leaf01442_w_row015_weighted
theorem leaf01442_w_row015_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01442_w_row015=true := by decide +kernel
#print axioms leaf01442_w_row015_weighted
#print axioms leaf01442_w_row015_identity
#print axioms leaf01442_w_row015_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
