/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Sources
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights27 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 81 leaf03800_w_segment27)
theorem leaf03800_w_weights27_identity : leaf03800_w_weights27=IntegerWeightedOuter.weights 4 1 4096 81 leaf03800_w_segment27 := by decide +kernel
noncomputable def leaf03800_w_piece27 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights27 leaf03800_w_segment27)
theorem leaf03800_w_piece27_weighted : leaf03800_w_piece27=IntegerWeightedOuter.applyWeights leaf03800_w_weights27 leaf03800_w_segment27 := by decide +kernel
theorem leaf03800_w_piece27_identity : leaf03800_w_piece27=IntegerOuterTerms.transform 4 1 4096 81 leaf03800_w_segment27 :=
  IntegerWeightedOuter.checked 4 1 4096 81 leaf03800_w_segment27 leaf03800_w_piece27 leaf03800_w_weights27 leaf03800_w_weights27_identity leaf03800_w_piece27_weighted
#print axioms leaf03800_w_weights27_identity
#print axioms leaf03800_w_piece27_weighted
#print axioms leaf03800_w_piece27_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
