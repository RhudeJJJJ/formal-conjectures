/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01677CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01677_w_row088 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01677_w_affine)
theorem leaf01677_w_row088_weighted : leaf01677_w_row088=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01677_w_affine := by decide +kernel
theorem leaf01677_w_row088_identity : leaf01677_w_row088=NestedInteger.coefficientFrom 88 88 0 leaf01677_w_affine :=
  IntegerWeightedBernstein.checked 88 88 0 leaf01677_w_affine leaf01677_w_row088 IntegerBernsteinWeights88.row088 (IntegerBernsteinTable.checked (n := 2) 88 88 0 89 leaf01677_w_affine IntegerBernsteinWeights88.row088 leaf01677_w_affine_length IntegerBernsteinWeights88.row088_identity) leaf01677_w_row088_weighted
theorem leaf01677_w_row088_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01677_w_row088=true := by decide +kernel
#print axioms leaf01677_w_row088_weighted
#print axioms leaf01677_w_row088_identity
#print axioms leaf01677_w_row088_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
