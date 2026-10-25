/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_row058 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf00000_w_affine)
theorem leaf00000_w_row058_weighted : leaf00000_w_row058=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf00000_w_affine := by decide +kernel
theorem leaf00000_w_row058_identity : leaf00000_w_row058=NestedInteger.coefficientFrom 88 58 0 leaf00000_w_affine :=
  IntegerWeightedBernstein.checked 88 58 0 leaf00000_w_affine leaf00000_w_row058 IntegerBernsteinWeights88.row058 (IntegerBernsteinTable.checked (n := 2) 88 58 0 89 leaf00000_w_affine IntegerBernsteinWeights88.row058 leaf00000_w_affine_length IntegerBernsteinWeights88.row058_identity) leaf00000_w_row058_weighted
theorem leaf00000_w_row058_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf00000_w_row058=true := by decide +kernel
#print axioms leaf00000_w_row058_weighted
#print axioms leaf00000_w_row058_identity
#print axioms leaf00000_w_row058_positive
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
