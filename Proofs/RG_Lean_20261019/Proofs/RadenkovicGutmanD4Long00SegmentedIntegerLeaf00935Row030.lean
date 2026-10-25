/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_row030 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf00935_w_affine)
theorem leaf00935_w_row030_weighted : leaf00935_w_row030=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf00935_w_affine := by decide +kernel
theorem leaf00935_w_row030_identity : leaf00935_w_row030=NestedInteger.coefficientFrom 88 30 0 leaf00935_w_affine :=
  IntegerWeightedBernstein.checked 88 30 0 leaf00935_w_affine leaf00935_w_row030 IntegerBernsteinWeights88.row030 (IntegerBernsteinTable.checked (n := 2) 88 30 0 89 leaf00935_w_affine IntegerBernsteinWeights88.row030 leaf00935_w_affine_length IntegerBernsteinWeights88.row030_identity) leaf00935_w_row030_weighted
theorem leaf00935_w_row030_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf00935_w_row030=true := by decide +kernel
#print axioms leaf00935_w_row030_weighted
#print axioms leaf00935_w_row030_identity
#print axioms leaf00935_w_row030_positive
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
