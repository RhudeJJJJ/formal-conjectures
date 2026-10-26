/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01438RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01438_w_row030 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01438_w_affine)
theorem leaf01438_w_row030_weighted : leaf01438_w_row030=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01438_w_affine := by decide +kernel
theorem leaf01438_w_row030_identity : leaf01438_w_row030=NestedInteger.coefficientFrom 88 30 0 leaf01438_w_affine :=
  IntegerWeightedBernstein.checked 88 30 0 leaf01438_w_affine leaf01438_w_row030 IntegerBernsteinWeights88.row030 (IntegerBernsteinTable.checked (n := 2) 88 30 0 89 leaf01438_w_affine IntegerBernsteinWeights88.row030 leaf01438_w_affine_length IntegerBernsteinWeights88.row030_identity) leaf01438_w_row030_weighted
theorem leaf01438_w_row030_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01438_w_row030=true := by decide +kernel
#print axioms leaf01438_w_row030_weighted
#print axioms leaf01438_w_row030_identity
#print axioms leaf01438_w_row030_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
