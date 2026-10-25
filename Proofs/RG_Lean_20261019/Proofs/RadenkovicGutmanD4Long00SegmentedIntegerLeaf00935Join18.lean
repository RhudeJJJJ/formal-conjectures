/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece18
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join19
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix18 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source19.length) leaf00935_w_piece18) leaf00935_w_suffix19)
theorem leaf00935_w_suffix18_join : leaf00935_w_suffix18=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source19.length) leaf00935_w_piece18) leaf00935_w_suffix19 := by decide +kernel
theorem leaf00935_w_suffix18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix18) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 54 leaf00935_w_source18)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 54 57
    leaf00935_w_segment18 leaf00935_w_source19 leaf00935_w_source18
    leaf00935_w_piece18 leaf00935_w_suffix19 leaf00935_w_suffix18
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source18)
    leaf00935_w_piece18_identity leaf00935_w_suffix19_eval leaf00935_w_suffix18_join x
#print axioms leaf00935_w_suffix18_join
#print axioms leaf00935_w_suffix18_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
