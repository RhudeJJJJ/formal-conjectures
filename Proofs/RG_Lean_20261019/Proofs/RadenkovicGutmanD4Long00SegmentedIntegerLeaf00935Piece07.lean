/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_weights07 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 2 1 2048 21 leaf00935_w_segment07)
theorem leaf00935_w_weights07_identity : leaf00935_w_weights07=IntegerWeightedOuter.weights 2 1 2048 21 leaf00935_w_segment07 := by decide +kernel
noncomputable def leaf00935_w_piece07 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00935_w_weights07 leaf00935_w_segment07)
theorem leaf00935_w_piece07_weighted : leaf00935_w_piece07=IntegerWeightedOuter.applyWeights leaf00935_w_weights07 leaf00935_w_segment07 := by decide +kernel
theorem leaf00935_w_piece07_identity : leaf00935_w_piece07=IntegerOuterTerms.transform 2 1 2048 21 leaf00935_w_segment07 :=
  IntegerWeightedOuter.checked 2 1 2048 21 leaf00935_w_segment07 leaf00935_w_piece07 leaf00935_w_weights07 leaf00935_w_weights07_identity leaf00935_w_piece07_weighted
#print axioms leaf00935_w_weights07_identity
#print axioms leaf00935_w_piece07_weighted
#print axioms leaf00935_w_piece07_identity
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
