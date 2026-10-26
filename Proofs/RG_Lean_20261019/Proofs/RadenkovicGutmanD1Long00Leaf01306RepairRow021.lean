/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01306RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01306_w_row021 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01306_w_affine)
theorem leaf01306_w_row021_weighted : leaf01306_w_row021=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01306_w_affine := by decide +kernel
theorem leaf01306_w_row021_identity : leaf01306_w_row021=NestedInteger.coefficientFrom 88 21 0 leaf01306_w_affine :=
  IntegerWeightedBernstein.checked 88 21 0 leaf01306_w_affine leaf01306_w_row021 IntegerBernsteinWeights88.row021 (IntegerBernsteinTable.checked (n := 2) 88 21 0 89 leaf01306_w_affine IntegerBernsteinWeights88.row021 leaf01306_w_affine_length IntegerBernsteinWeights88.row021_identity) leaf01306_w_row021_weighted
theorem leaf01306_w_row021_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01306_w_row021=true := by decide +kernel
#print axioms leaf01306_w_row021_weighted
#print axioms leaf01306_w_row021_identity
#print axioms leaf01306_w_row021_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
