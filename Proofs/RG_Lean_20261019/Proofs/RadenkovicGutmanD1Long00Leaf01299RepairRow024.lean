/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01299RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01299_w_row024 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01299_w_affine)
theorem leaf01299_w_row024_weighted : leaf01299_w_row024=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01299_w_affine := by decide +kernel
theorem leaf01299_w_row024_identity : leaf01299_w_row024=NestedInteger.coefficientFrom 88 24 0 leaf01299_w_affine :=
  IntegerWeightedBernstein.checked 88 24 0 leaf01299_w_affine leaf01299_w_row024 IntegerBernsteinWeights88.row024 (IntegerBernsteinTable.checked (n := 2) 88 24 0 89 leaf01299_w_affine IntegerBernsteinWeights88.row024 leaf01299_w_affine_length IntegerBernsteinWeights88.row024_identity) leaf01299_w_row024_weighted
theorem leaf01299_w_row024_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01299_w_row024=true := by decide +kernel
#print axioms leaf01299_w_row024_weighted
#print axioms leaf01299_w_row024_identity
#print axioms leaf01299_w_row024_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
