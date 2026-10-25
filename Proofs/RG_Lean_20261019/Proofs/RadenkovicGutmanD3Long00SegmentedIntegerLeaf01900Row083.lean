/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_row083 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01900_w_affine)
theorem leaf01900_w_row083_weighted : leaf01900_w_row083=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01900_w_affine := by decide +kernel
theorem leaf01900_w_row083_identity : leaf01900_w_row083=NestedInteger.coefficientFrom 88 83 0 leaf01900_w_affine :=
  IntegerWeightedBernstein.checked 88 83 0 leaf01900_w_affine leaf01900_w_row083 IntegerBernsteinWeights88.row083 (IntegerBernsteinTable.checked (n := 2) 88 83 0 89 leaf01900_w_affine IntegerBernsteinWeights88.row083 leaf01900_w_affine_length IntegerBernsteinWeights88.row083_identity) leaf01900_w_row083_weighted
theorem leaf01900_w_row083_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01900_w_row083=true := by decide +kernel
#print axioms leaf01900_w_row083_weighted
#print axioms leaf01900_w_row083_identity
#print axioms leaf01900_w_row083_positive
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
