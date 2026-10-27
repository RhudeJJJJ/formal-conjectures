/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01503RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01503_w_row084 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01503_w_affine)
theorem leaf01503_w_row084_weighted : leaf01503_w_row084=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01503_w_affine := by decide +kernel
theorem leaf01503_w_row084_identity : leaf01503_w_row084=NestedInteger.coefficientFrom 88 84 0 leaf01503_w_affine :=
  IntegerWeightedBernstein.checked 88 84 0 leaf01503_w_affine leaf01503_w_row084 IntegerBernsteinWeights88.row084 (IntegerBernsteinTable.checked (n := 2) 88 84 0 89 leaf01503_w_affine IntegerBernsteinWeights88.row084 leaf01503_w_affine_length IntegerBernsteinWeights88.row084_identity) leaf01503_w_row084_weighted
theorem leaf01503_w_row084_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01503_w_row084=true := by decide +kernel
#print axioms leaf01503_w_row084_weighted
#print axioms leaf01503_w_row084_identity
#print axioms leaf01503_w_row084_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
