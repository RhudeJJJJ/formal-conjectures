/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_row034 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf00000_w_affine)
theorem leaf00000_w_row034_weighted : leaf00000_w_row034=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf00000_w_affine := by decide +kernel
theorem leaf00000_w_row034_identity : leaf00000_w_row034=NestedInteger.coefficientFrom 88 34 0 leaf00000_w_affine :=
  IntegerWeightedBernstein.checked 88 34 0 leaf00000_w_affine leaf00000_w_row034 IntegerBernsteinWeights88.row034 (IntegerBernsteinTable.checked (n := 2) 88 34 0 89 leaf00000_w_affine IntegerBernsteinWeights88.row034 leaf00000_w_affine_length IntegerBernsteinWeights88.row034_identity) leaf00000_w_row034_weighted
theorem leaf00000_w_row034_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf00000_w_row034=true := by decide +kernel
#print axioms leaf00000_w_row034_weighted
#print axioms leaf00000_w_row034_identity
#print axioms leaf00000_w_row034_positive
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
