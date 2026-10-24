/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedAffineLength
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_row032 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01260_w_affine)
theorem leaf01260_w_row032_weighted : leaf01260_w_row032=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row032_identity : leaf01260_w_row032=NestedInteger.coefficientFrom 88 32 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 32 0 leaf01260_w_affine leaf01260_w_row032 IntegerBernsteinWeights88.row032 (IntegerBernsteinTable.checked (n := 2) 88 32 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row032 leaf01260_w_affine_length IntegerBernsteinWeights88.row032_identity) leaf01260_w_row032_weighted
theorem leaf01260_w_row032_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row032=true := by decide +kernel
#print axioms leaf01260_w_row032_weighted
#print axioms leaf01260_w_row032_identity
#print axioms leaf01260_w_row032_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
