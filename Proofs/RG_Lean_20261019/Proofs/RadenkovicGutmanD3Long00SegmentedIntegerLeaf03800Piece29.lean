/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Sources
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights29 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 87 leaf03800_w_segment29)
theorem leaf03800_w_weights29_identity : leaf03800_w_weights29=IntegerWeightedOuter.weights 4 1 4096 87 leaf03800_w_segment29 := by decide +kernel
noncomputable def leaf03800_w_piece29 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights29 leaf03800_w_segment29)
theorem leaf03800_w_piece29_weighted : leaf03800_w_piece29=IntegerWeightedOuter.applyWeights leaf03800_w_weights29 leaf03800_w_segment29 := by decide +kernel
theorem leaf03800_w_piece29_identity : leaf03800_w_piece29=IntegerOuterTerms.transform 4 1 4096 87 leaf03800_w_segment29 :=
  IntegerWeightedOuter.checked 4 1 4096 87 leaf03800_w_segment29 leaf03800_w_piece29 leaf03800_w_weights29 leaf03800_w_weights29_identity leaf03800_w_piece29_weighted
#print axioms leaf03800_w_weights29_identity
#print axioms leaf03800_w_piece29_weighted
#print axioms leaf03800_w_piece29_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
