/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01672CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01672_w_row042 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01672_w_affine)
theorem leaf01672_w_row042_weighted : leaf01672_w_row042=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01672_w_affine := by decide +kernel
theorem leaf01672_w_row042_identity : leaf01672_w_row042=NestedInteger.coefficientFrom 88 42 0 leaf01672_w_affine :=
  IntegerWeightedBernstein.checked 88 42 0 leaf01672_w_affine leaf01672_w_row042 IntegerBernsteinWeights88.row042 (IntegerBernsteinTable.checked (n := 2) 88 42 0 89 leaf01672_w_affine IntegerBernsteinWeights88.row042 leaf01672_w_affine_length IntegerBernsteinWeights88.row042_identity) leaf01672_w_row042_weighted
theorem leaf01672_w_row042_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01672_w_row042=true := by decide +kernel
#print axioms leaf01672_w_row042_weighted
#print axioms leaf01672_w_row042_identity
#print axioms leaf01672_w_row042_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
