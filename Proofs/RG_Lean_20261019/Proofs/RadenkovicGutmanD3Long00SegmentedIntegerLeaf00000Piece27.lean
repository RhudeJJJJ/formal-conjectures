/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_weights27 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 32 1 32000 81 leaf00000_w_segment27)
theorem leaf00000_w_weights27_identity : leaf00000_w_weights27=IntegerWeightedOuter.weights 32 1 32000 81 leaf00000_w_segment27 := by decide +kernel
noncomputable def leaf00000_w_piece27 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00000_w_weights27 leaf00000_w_segment27)
theorem leaf00000_w_piece27_weighted : leaf00000_w_piece27=IntegerWeightedOuter.applyWeights leaf00000_w_weights27 leaf00000_w_segment27 := by decide +kernel
theorem leaf00000_w_piece27_identity : leaf00000_w_piece27=IntegerOuterTerms.transform 32 1 32000 81 leaf00000_w_segment27 :=
  IntegerWeightedOuter.checked 32 1 32000 81 leaf00000_w_segment27 leaf00000_w_piece27 leaf00000_w_weights27 leaf00000_w_weights27_identity leaf00000_w_piece27_weighted
#print axioms leaf00000_w_weights27_identity
#print axioms leaf00000_w_piece27_weighted
#print axioms leaf00000_w_piece27_identity
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
