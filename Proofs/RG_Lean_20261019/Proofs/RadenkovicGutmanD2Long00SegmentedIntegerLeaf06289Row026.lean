/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_row026 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf06289_w_affine)
theorem leaf06289_w_row026_weighted : leaf06289_w_row026=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf06289_w_affine := by decide +kernel
theorem leaf06289_w_row026_identity : leaf06289_w_row026=NestedInteger.coefficientFrom 88 26 0 leaf06289_w_affine :=
  IntegerWeightedBernstein.checked 88 26 0 leaf06289_w_affine leaf06289_w_row026 IntegerBernsteinWeights88.row026 (IntegerBernsteinTable.checked (n := 2) 88 26 0 89 leaf06289_w_affine IntegerBernsteinWeights88.row026 leaf06289_w_affine_length IntegerBernsteinWeights88.row026_identity) leaf06289_w_row026_weighted
theorem leaf06289_w_row026_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf06289_w_row026=true := by decide +kernel
#print axioms leaf06289_w_row026_weighted
#print axioms leaf06289_w_row026_identity
#print axioms leaf06289_w_row026_positive
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
