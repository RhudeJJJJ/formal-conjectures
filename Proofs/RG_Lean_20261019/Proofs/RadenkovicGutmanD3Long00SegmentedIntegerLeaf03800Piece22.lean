/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Sources
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights22 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 66 leaf03800_w_segment22)
theorem leaf03800_w_weights22_identity : leaf03800_w_weights22=IntegerWeightedOuter.weights 4 1 4096 66 leaf03800_w_segment22 := by decide +kernel
noncomputable def leaf03800_w_piece22 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights22 leaf03800_w_segment22)
theorem leaf03800_w_piece22_weighted : leaf03800_w_piece22=IntegerWeightedOuter.applyWeights leaf03800_w_weights22 leaf03800_w_segment22 := by decide +kernel
theorem leaf03800_w_piece22_identity : leaf03800_w_piece22=IntegerOuterTerms.transform 4 1 4096 66 leaf03800_w_segment22 :=
  IntegerWeightedOuter.checked 4 1 4096 66 leaf03800_w_segment22 leaf03800_w_piece22 leaf03800_w_weights22 leaf03800_w_weights22_identity leaf03800_w_piece22_weighted
#print axioms leaf03800_w_weights22_identity
#print axioms leaf03800_w_piece22_weighted
#print axioms leaf03800_w_piece22_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
