/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece20
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join21
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source21.length) leaf00935_w_piece20) leaf00935_w_suffix21)
theorem leaf00935_w_suffix20_join : leaf00935_w_suffix20=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source21.length) leaf00935_w_piece20) leaf00935_w_suffix21 := by decide +kernel
theorem leaf00935_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 60 leaf00935_w_source20)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 60 63
    leaf00935_w_segment20 leaf00935_w_source21 leaf00935_w_source20
    leaf00935_w_piece20 leaf00935_w_suffix21 leaf00935_w_suffix20
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source20)
    leaf00935_w_piece20_identity leaf00935_w_suffix21_eval leaf00935_w_suffix20_join x
#print axioms leaf00935_w_suffix20_join
#print axioms leaf00935_w_suffix20_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
