/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece00
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join01
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source01.length) leaf00935_w_piece00) leaf00935_w_suffix01)
theorem leaf00935_w_affine_join : leaf00935_w_affine=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source01.length) leaf00935_w_piece00) leaf00935_w_suffix01 := by decide +kernel
theorem leaf00935_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 0 leaf00935_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 0 3
    leaf00935_w_segment00 leaf00935_w_source01 leaf00935_w_source00
    leaf00935_w_piece00 leaf00935_w_suffix01 leaf00935_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source00)
    leaf00935_w_piece00_identity leaf00935_w_suffix01_eval leaf00935_w_affine_join x
#print axioms leaf00935_w_affine_join
#print axioms leaf00935_w_affine_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
