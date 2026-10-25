/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_row017 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf00000_w_affine)
theorem leaf00000_w_row017_weighted : leaf00000_w_row017=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf00000_w_affine := by decide +kernel
theorem leaf00000_w_row017_identity : leaf00000_w_row017=NestedInteger.coefficientFrom 88 17 0 leaf00000_w_affine :=
  IntegerWeightedBernstein.checked 88 17 0 leaf00000_w_affine leaf00000_w_row017 IntegerBernsteinWeights88.row017 (IntegerBernsteinTable.checked (n := 2) 88 17 0 89 leaf00000_w_affine IntegerBernsteinWeights88.row017 leaf00000_w_affine_length IntegerBernsteinWeights88.row017_identity) leaf00000_w_row017_weighted
theorem leaf00000_w_row017_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf00000_w_row017=true := by decide +kernel
#print axioms leaf00000_w_row017_weighted
#print axioms leaf00000_w_row017_identity
#print axioms leaf00000_w_row017_positive
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
