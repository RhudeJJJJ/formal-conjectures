/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_weights25 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 2 1 2048 75 leaf00935_w_segment25)
theorem leaf00935_w_weights25_identity : leaf00935_w_weights25=IntegerWeightedOuter.weights 2 1 2048 75 leaf00935_w_segment25 := by decide +kernel
noncomputable def leaf00935_w_piece25 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00935_w_weights25 leaf00935_w_segment25)
theorem leaf00935_w_piece25_weighted : leaf00935_w_piece25=IntegerWeightedOuter.applyWeights leaf00935_w_weights25 leaf00935_w_segment25 := by decide +kernel
theorem leaf00935_w_piece25_identity : leaf00935_w_piece25=IntegerOuterTerms.transform 2 1 2048 75 leaf00935_w_segment25 :=
  IntegerWeightedOuter.checked 2 1 2048 75 leaf00935_w_segment25 leaf00935_w_piece25 leaf00935_w_weights25 leaf00935_w_weights25_identity leaf00935_w_piece25_weighted
#print axioms leaf00935_w_weights25_identity
#print axioms leaf00935_w_piece25_weighted
#print axioms leaf00935_w_piece25_identity
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
