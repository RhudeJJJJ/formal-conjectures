/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289AffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_row082 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf06289_w_affine)
theorem leaf06289_w_row082_weighted : leaf06289_w_row082=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf06289_w_affine := by decide +kernel
theorem leaf06289_w_row082_identity : leaf06289_w_row082=NestedInteger.coefficientFrom 88 82 0 leaf06289_w_affine :=
  IntegerWeightedBernstein.checked 88 82 0 leaf06289_w_affine leaf06289_w_row082 IntegerBernsteinWeights88.row082 (IntegerBernsteinTable.checked (n := 2) 88 82 0 89 leaf06289_w_affine IntegerBernsteinWeights88.row082 leaf06289_w_affine_length IntegerBernsteinWeights88.row082_identity) leaf06289_w_row082_weighted
theorem leaf06289_w_row082_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf06289_w_row082=true := by decide +kernel
#print axioms leaf06289_w_row082_weighted
#print axioms leaf06289_w_row082_identity
#print axioms leaf06289_w_row082_positive
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
