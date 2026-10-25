/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece26
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source27.length) leaf00935_w_piece26) leaf00935_w_suffix27)
theorem leaf00935_w_suffix26_join : leaf00935_w_suffix26=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source27.length) leaf00935_w_piece26) leaf00935_w_suffix27 := by decide +kernel
theorem leaf00935_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 78 leaf00935_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 78 81
    leaf00935_w_segment26 leaf00935_w_source27 leaf00935_w_source26
    leaf00935_w_piece26 leaf00935_w_suffix27 leaf00935_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source26)
    leaf00935_w_piece26_identity leaf00935_w_suffix27_eval leaf00935_w_suffix26_join x
#print axioms leaf00935_w_suffix26_join
#print axioms leaf00935_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
