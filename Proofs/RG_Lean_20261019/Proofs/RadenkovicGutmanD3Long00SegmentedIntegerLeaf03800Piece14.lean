/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Sources
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights14 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 42 leaf03800_w_segment14)
theorem leaf03800_w_weights14_identity : leaf03800_w_weights14=IntegerWeightedOuter.weights 4 1 4096 42 leaf03800_w_segment14 := by decide +kernel
noncomputable def leaf03800_w_piece14 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights14 leaf03800_w_segment14)
theorem leaf03800_w_piece14_weighted : leaf03800_w_piece14=IntegerWeightedOuter.applyWeights leaf03800_w_weights14 leaf03800_w_segment14 := by decide +kernel
theorem leaf03800_w_piece14_identity : leaf03800_w_piece14=IntegerOuterTerms.transform 4 1 4096 42 leaf03800_w_segment14 :=
  IntegerWeightedOuter.checked 4 1 4096 42 leaf03800_w_segment14 leaf03800_w_piece14 leaf03800_w_weights14 leaf03800_w_weights14_identity leaf03800_w_piece14_weighted
#print axioms leaf03800_w_weights14_identity
#print axioms leaf03800_w_piece14_weighted
#print axioms leaf03800_w_piece14_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
