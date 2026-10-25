/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece08
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join09
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix08 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source09.length) leaf00935_w_piece08) leaf00935_w_suffix09)
theorem leaf00935_w_suffix08_join : leaf00935_w_suffix08=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source09.length) leaf00935_w_piece08) leaf00935_w_suffix09 := by decide +kernel
theorem leaf00935_w_suffix08_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix08) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 24 leaf00935_w_source08)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 24 27
    leaf00935_w_segment08 leaf00935_w_source09 leaf00935_w_source08
    leaf00935_w_piece08 leaf00935_w_suffix09 leaf00935_w_suffix08
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source08)
    leaf00935_w_piece08_identity leaf00935_w_suffix09_eval leaf00935_w_suffix08_join x
#print axioms leaf00935_w_suffix08_join
#print axioms leaf00935_w_suffix08_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
