/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_weights03 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 2 1 2048 9 leaf00935_w_segment03)
theorem leaf00935_w_weights03_identity : leaf00935_w_weights03=IntegerWeightedOuter.weights 2 1 2048 9 leaf00935_w_segment03 := by decide +kernel
noncomputable def leaf00935_w_piece03 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00935_w_weights03 leaf00935_w_segment03)
theorem leaf00935_w_piece03_weighted : leaf00935_w_piece03=IntegerWeightedOuter.applyWeights leaf00935_w_weights03 leaf00935_w_segment03 := by decide +kernel
theorem leaf00935_w_piece03_identity : leaf00935_w_piece03=IntegerOuterTerms.transform 2 1 2048 9 leaf00935_w_segment03 :=
  IntegerWeightedOuter.checked 2 1 2048 9 leaf00935_w_segment03 leaf00935_w_piece03 leaf00935_w_weights03 leaf00935_w_weights03_identity leaf00935_w_piece03_weighted
#print axioms leaf00935_w_weights03_identity
#print axioms leaf00935_w_piece03_weighted
#print axioms leaf00935_w_piece03_identity
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
