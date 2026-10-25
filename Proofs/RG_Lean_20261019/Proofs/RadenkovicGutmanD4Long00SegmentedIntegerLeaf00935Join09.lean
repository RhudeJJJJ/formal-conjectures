/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece09
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join10
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source10.length) leaf00935_w_piece09) leaf00935_w_suffix10)
theorem leaf00935_w_suffix09_join : leaf00935_w_suffix09=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source10.length) leaf00935_w_piece09) leaf00935_w_suffix10 := by decide +kernel
theorem leaf00935_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 27 leaf00935_w_source09)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 27 30
    leaf00935_w_segment09 leaf00935_w_source10 leaf00935_w_source09
    leaf00935_w_piece09 leaf00935_w_suffix10 leaf00935_w_suffix09
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source09)
    leaf00935_w_piece09_identity leaf00935_w_suffix10_eval leaf00935_w_suffix09_join x
#print axioms leaf00935_w_suffix09_join
#print axioms leaf00935_w_suffix09_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
