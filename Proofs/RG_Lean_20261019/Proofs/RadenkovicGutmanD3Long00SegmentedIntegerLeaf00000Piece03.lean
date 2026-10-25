/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_weights03 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 32 1 32000 9 leaf00000_w_segment03)
theorem leaf00000_w_weights03_identity : leaf00000_w_weights03=IntegerWeightedOuter.weights 32 1 32000 9 leaf00000_w_segment03 := by decide +kernel
noncomputable def leaf00000_w_piece03 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00000_w_weights03 leaf00000_w_segment03)
theorem leaf00000_w_piece03_weighted : leaf00000_w_piece03=IntegerWeightedOuter.applyWeights leaf00000_w_weights03 leaf00000_w_segment03 := by decide +kernel
theorem leaf00000_w_piece03_identity : leaf00000_w_piece03=IntegerOuterTerms.transform 32 1 32000 9 leaf00000_w_segment03 :=
  IntegerWeightedOuter.checked 32 1 32000 9 leaf00000_w_segment03 leaf00000_w_piece03 leaf00000_w_weights03 leaf00000_w_weights03_identity leaf00000_w_piece03_weighted
#print axioms leaf00000_w_weights03_identity
#print axioms leaf00000_w_piece03_weighted
#print axioms leaf00000_w_piece03_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
