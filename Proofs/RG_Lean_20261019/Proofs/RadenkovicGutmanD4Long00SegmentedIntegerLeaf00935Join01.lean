/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece01
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source02.length) leaf00935_w_piece01) leaf00935_w_suffix02)
theorem leaf00935_w_suffix01_join : leaf00935_w_suffix01=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source02.length) leaf00935_w_piece01) leaf00935_w_suffix02 := by decide +kernel
theorem leaf00935_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 3 leaf00935_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 3 6
    leaf00935_w_segment01 leaf00935_w_source02 leaf00935_w_source01
    leaf00935_w_piece01 leaf00935_w_suffix02 leaf00935_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source01)
    leaf00935_w_piece01_identity leaf00935_w_suffix02_eval leaf00935_w_suffix01_join x
#print axioms leaf00935_w_suffix01_join
#print axioms leaf00935_w_suffix01_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
