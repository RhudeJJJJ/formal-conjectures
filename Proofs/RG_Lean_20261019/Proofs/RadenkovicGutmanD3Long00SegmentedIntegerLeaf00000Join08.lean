/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Piece08
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Join09
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix08 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source09.length) leaf00000_w_piece08) leaf00000_w_suffix09)
theorem leaf00000_w_suffix08_join : leaf00000_w_suffix08=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source09.length) leaf00000_w_piece08) leaf00000_w_suffix09 := by decide +kernel
theorem leaf00000_w_suffix08_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix08) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 24 leaf00000_w_source08)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 24 27
    leaf00000_w_segment08 leaf00000_w_source09 leaf00000_w_source08
    leaf00000_w_piece08 leaf00000_w_suffix09 leaf00000_w_suffix08
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source08)
    leaf00000_w_piece08_identity leaf00000_w_suffix09_eval leaf00000_w_suffix08_join x
#print axioms leaf00000_w_suffix08_join
#print axioms leaf00000_w_suffix08_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
