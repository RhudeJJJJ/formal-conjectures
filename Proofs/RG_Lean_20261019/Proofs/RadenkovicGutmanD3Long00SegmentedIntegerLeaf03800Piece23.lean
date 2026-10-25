/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Sources
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights23 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 69 leaf03800_w_segment23)
theorem leaf03800_w_weights23_identity : leaf03800_w_weights23=IntegerWeightedOuter.weights 4 1 4096 69 leaf03800_w_segment23 := by decide +kernel
noncomputable def leaf03800_w_piece23 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights23 leaf03800_w_segment23)
theorem leaf03800_w_piece23_weighted : leaf03800_w_piece23=IntegerWeightedOuter.applyWeights leaf03800_w_weights23 leaf03800_w_segment23 := by decide +kernel
theorem leaf03800_w_piece23_identity : leaf03800_w_piece23=IntegerOuterTerms.transform 4 1 4096 69 leaf03800_w_segment23 :=
  IntegerWeightedOuter.checked 4 1 4096 69 leaf03800_w_segment23 leaf03800_w_piece23 leaf03800_w_weights23 leaf03800_w_weights23_identity leaf03800_w_piece23_weighted
#print axioms leaf03800_w_weights23_identity
#print axioms leaf03800_w_piece23_weighted
#print axioms leaf03800_w_piece23_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
