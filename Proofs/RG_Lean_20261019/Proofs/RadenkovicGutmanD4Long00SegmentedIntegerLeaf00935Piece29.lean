/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_weights29 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 2 1 2048 87 leaf00935_w_segment29)
theorem leaf00935_w_weights29_identity : leaf00935_w_weights29=IntegerWeightedOuter.weights 2 1 2048 87 leaf00935_w_segment29 := by decide +kernel
noncomputable def leaf00935_w_piece29 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00935_w_weights29 leaf00935_w_segment29)
theorem leaf00935_w_piece29_weighted : leaf00935_w_piece29=IntegerWeightedOuter.applyWeights leaf00935_w_weights29 leaf00935_w_segment29 := by decide +kernel
theorem leaf00935_w_piece29_identity : leaf00935_w_piece29=IntegerOuterTerms.transform 2 1 2048 87 leaf00935_w_segment29 :=
  IntegerWeightedOuter.checked 2 1 2048 87 leaf00935_w_segment29 leaf00935_w_piece29 leaf00935_w_weights29 leaf00935_w_weights29_identity leaf00935_w_piece29_weighted
#print axioms leaf00935_w_weights29_identity
#print axioms leaf00935_w_piece29_weighted
#print axioms leaf00935_w_piece29_identity
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
