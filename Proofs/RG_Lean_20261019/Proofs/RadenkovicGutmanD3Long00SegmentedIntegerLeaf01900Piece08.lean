/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_weights08 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 559 3 12800 24 leaf01900_w_segment08)
theorem leaf01900_w_weights08_identity : leaf01900_w_weights08=IntegerWeightedOuter.weights 559 3 12800 24 leaf01900_w_segment08 := by decide +kernel
noncomputable def leaf01900_w_piece08 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01900_w_weights08 leaf01900_w_segment08)
theorem leaf01900_w_piece08_weighted : leaf01900_w_piece08=IntegerWeightedOuter.applyWeights leaf01900_w_weights08 leaf01900_w_segment08 := by decide +kernel
theorem leaf01900_w_piece08_identity : leaf01900_w_piece08=IntegerOuterTerms.transform 559 3 12800 24 leaf01900_w_segment08 :=
  IntegerWeightedOuter.checked 559 3 12800 24 leaf01900_w_segment08 leaf01900_w_piece08 leaf01900_w_weights08 leaf01900_w_weights08_identity leaf01900_w_piece08_weighted
#print axioms leaf01900_w_weights08_identity
#print axioms leaf01900_w_piece08_weighted
#print axioms leaf01900_w_piece08_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
