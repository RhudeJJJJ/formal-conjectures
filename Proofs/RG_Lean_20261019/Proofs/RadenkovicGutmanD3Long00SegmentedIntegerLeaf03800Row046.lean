/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800AffineLength
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_row046 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf03800_w_affine)
theorem leaf03800_w_row046_weighted : leaf03800_w_row046=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf03800_w_affine := by decide +kernel
theorem leaf03800_w_row046_identity : leaf03800_w_row046=NestedInteger.coefficientFrom 88 46 0 leaf03800_w_affine :=
  IntegerWeightedBernstein.checked 88 46 0 leaf03800_w_affine leaf03800_w_row046 IntegerBernsteinWeights88.row046 (IntegerBernsteinTable.checked (n := 2) 88 46 0 89 leaf03800_w_affine IntegerBernsteinWeights88.row046 leaf03800_w_affine_length IntegerBernsteinWeights88.row046_identity) leaf03800_w_row046_weighted
theorem leaf03800_w_row046_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf03800_w_row046=true := by decide +kernel
#print axioms leaf03800_w_row046_weighted
#print axioms leaf03800_w_row046_identity
#print axioms leaf03800_w_row046_positive
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
