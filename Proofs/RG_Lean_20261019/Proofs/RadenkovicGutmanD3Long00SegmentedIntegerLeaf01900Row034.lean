/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_row034 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01900_w_affine)
theorem leaf01900_w_row034_weighted : leaf01900_w_row034=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01900_w_affine := by decide +kernel
theorem leaf01900_w_row034_identity : leaf01900_w_row034=NestedInteger.coefficientFrom 88 34 0 leaf01900_w_affine :=
  IntegerWeightedBernstein.checked 88 34 0 leaf01900_w_affine leaf01900_w_row034 IntegerBernsteinWeights88.row034 (IntegerBernsteinTable.checked (n := 2) 88 34 0 89 leaf01900_w_affine IntegerBernsteinWeights88.row034 leaf01900_w_affine_length IntegerBernsteinWeights88.row034_identity) leaf01900_w_row034_weighted
theorem leaf01900_w_row034_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01900_w_row034=true := by decide +kernel
#print axioms leaf01900_w_row034_weighted
#print axioms leaf01900_w_row034_identity
#print axioms leaf01900_w_row034_positive
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
