/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece28
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix28 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source29.length) leaf00935_w_piece28) leaf00935_w_suffix29)
theorem leaf00935_w_suffix28_join : leaf00935_w_suffix28=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source29.length) leaf00935_w_piece28) leaf00935_w_suffix29 := by decide +kernel
theorem leaf00935_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 84 leaf00935_w_source28)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 84 87
    leaf00935_w_segment28 leaf00935_w_source29 leaf00935_w_source28
    leaf00935_w_piece28 leaf00935_w_suffix29 leaf00935_w_suffix28
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source28)
    leaf00935_w_piece28_identity leaf00935_w_suffix29_eval leaf00935_w_suffix28_join x
#print axioms leaf00935_w_suffix28_join
#print axioms leaf00935_w_suffix28_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
