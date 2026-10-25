/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_weights24 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 2 1 2048 72 leaf00935_w_segment24)
theorem leaf00935_w_weights24_identity : leaf00935_w_weights24=IntegerWeightedOuter.weights 2 1 2048 72 leaf00935_w_segment24 := by decide +kernel
noncomputable def leaf00935_w_piece24 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00935_w_weights24 leaf00935_w_segment24)
theorem leaf00935_w_piece24_weighted : leaf00935_w_piece24=IntegerWeightedOuter.applyWeights leaf00935_w_weights24 leaf00935_w_segment24 := by decide +kernel
theorem leaf00935_w_piece24_identity : leaf00935_w_piece24=IntegerOuterTerms.transform 2 1 2048 72 leaf00935_w_segment24 :=
  IntegerWeightedOuter.checked 2 1 2048 72 leaf00935_w_segment24 leaf00935_w_piece24 leaf00935_w_weights24 leaf00935_w_weights24_identity leaf00935_w_piece24_weighted
#print axioms leaf00935_w_weights24_identity
#print axioms leaf00935_w_piece24_weighted
#print axioms leaf00935_w_piece24_identity
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
