/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Piece27
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Join28
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source28.length) leaf00000_w_piece27) leaf00000_w_suffix28)
theorem leaf00000_w_suffix27_join : leaf00000_w_suffix27=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source28.length) leaf00000_w_piece27) leaf00000_w_suffix28 := by decide +kernel
theorem leaf00000_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 81 leaf00000_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 81 84
    leaf00000_w_segment27 leaf00000_w_source28 leaf00000_w_source27
    leaf00000_w_piece27 leaf00000_w_suffix28 leaf00000_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source27)
    leaf00000_w_piece27_identity leaf00000_w_suffix28_eval leaf00000_w_suffix27_join x
#print axioms leaf00000_w_suffix27_join
#print axioms leaf00000_w_suffix27_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
