/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01409RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01409_w_row066 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01409_w_affine)
theorem leaf01409_w_row066_weighted : leaf01409_w_row066=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01409_w_affine := by decide +kernel
theorem leaf01409_w_row066_identity : leaf01409_w_row066=NestedInteger.coefficientFrom 88 66 0 leaf01409_w_affine :=
  IntegerWeightedBernstein.checked 88 66 0 leaf01409_w_affine leaf01409_w_row066 IntegerBernsteinWeights88.row066 (IntegerBernsteinTable.checked (n := 2) 88 66 0 89 leaf01409_w_affine IntegerBernsteinWeights88.row066 leaf01409_w_affine_length IntegerBernsteinWeights88.row066_identity) leaf01409_w_row066_weighted
theorem leaf01409_w_row066_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01409_w_row066=true := by decide +kernel
#print axioms leaf01409_w_row066_weighted
#print axioms leaf01409_w_row066_identity
#print axioms leaf01409_w_row066_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
