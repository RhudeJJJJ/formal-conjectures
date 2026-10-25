/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece27
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join28
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source28.length) leaf00935_w_piece27) leaf00935_w_suffix28)
theorem leaf00935_w_suffix27_join : leaf00935_w_suffix27=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source28.length) leaf00935_w_piece27) leaf00935_w_suffix28 := by decide +kernel
theorem leaf00935_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 81 leaf00935_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 81 84
    leaf00935_w_segment27 leaf00935_w_source28 leaf00935_w_source27
    leaf00935_w_piece27 leaf00935_w_suffix28 leaf00935_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source27)
    leaf00935_w_piece27_identity leaf00935_w_suffix28_eval leaf00935_w_suffix27_join x
#print axioms leaf00935_w_suffix27_join
#print axioms leaf00935_w_suffix27_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
