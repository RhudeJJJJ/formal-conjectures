/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece06
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join07
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix06 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source07.length) leaf00935_w_piece06) leaf00935_w_suffix07)
theorem leaf00935_w_suffix06_join : leaf00935_w_suffix06=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source07.length) leaf00935_w_piece06) leaf00935_w_suffix07 := by decide +kernel
theorem leaf00935_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 18 leaf00935_w_source06)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 18 21
    leaf00935_w_segment06 leaf00935_w_source07 leaf00935_w_source06
    leaf00935_w_piece06 leaf00935_w_suffix07 leaf00935_w_suffix06
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source06)
    leaf00935_w_piece06_identity leaf00935_w_suffix07_eval leaf00935_w_suffix06_join x
#print axioms leaf00935_w_suffix06_join
#print axioms leaf00935_w_suffix06_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
