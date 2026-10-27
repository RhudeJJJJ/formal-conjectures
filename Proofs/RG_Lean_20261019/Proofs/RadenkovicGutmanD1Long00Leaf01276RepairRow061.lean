/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01276RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01276_w_row061 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01276_w_affine)
theorem leaf01276_w_row061_weighted : leaf01276_w_row061=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01276_w_affine := by decide +kernel
theorem leaf01276_w_row061_identity : leaf01276_w_row061=NestedInteger.coefficientFrom 88 61 0 leaf01276_w_affine :=
  IntegerWeightedBernstein.checked 88 61 0 leaf01276_w_affine leaf01276_w_row061 IntegerBernsteinWeights88.row061 (IntegerBernsteinTable.checked (n := 2) 88 61 0 89 leaf01276_w_affine IntegerBernsteinWeights88.row061 leaf01276_w_affine_length IntegerBernsteinWeights88.row061_identity) leaf01276_w_row061_weighted
theorem leaf01276_w_row061_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01276_w_row061=true := by decide +kernel
#print axioms leaf01276_w_row061_weighted
#print axioms leaf01276_w_row061_identity
#print axioms leaf01276_w_row061_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
