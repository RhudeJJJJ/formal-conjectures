/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_weights01 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 2 1 2048 3 leaf00935_w_segment01)
theorem leaf00935_w_weights01_identity : leaf00935_w_weights01=IntegerWeightedOuter.weights 2 1 2048 3 leaf00935_w_segment01 := by decide +kernel
noncomputable def leaf00935_w_piece01 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00935_w_weights01 leaf00935_w_segment01)
theorem leaf00935_w_piece01_weighted : leaf00935_w_piece01=IntegerWeightedOuter.applyWeights leaf00935_w_weights01 leaf00935_w_segment01 := by decide +kernel
theorem leaf00935_w_piece01_identity : leaf00935_w_piece01=IntegerOuterTerms.transform 2 1 2048 3 leaf00935_w_segment01 :=
  IntegerWeightedOuter.checked 2 1 2048 3 leaf00935_w_segment01 leaf00935_w_piece01 leaf00935_w_weights01 leaf00935_w_weights01_identity leaf00935_w_piece01_weighted
#print axioms leaf00935_w_weights01_identity
#print axioms leaf00935_w_piece01_weighted
#print axioms leaf00935_w_piece01_identity
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
