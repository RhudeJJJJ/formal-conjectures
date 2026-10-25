/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece11
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Join12
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix11 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source12.length) leaf00935_w_piece11) leaf00935_w_suffix12)
theorem leaf00935_w_suffix11_join : leaf00935_w_suffix11=NestedInteger.add (NestedInteger.scale (2048^leaf00935_w_source12.length) leaf00935_w_piece11) leaf00935_w_suffix12 := by decide +kernel
theorem leaf00935_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 33 leaf00935_w_source11)) x :=
  IntegerOuterJoinedEvaluation.joined 2 1 2048 33 36
    leaf00935_w_segment11 leaf00935_w_source12 leaf00935_w_source11
    leaf00935_w_piece11 leaf00935_w_suffix12 leaf00935_w_suffix11
    (by decide +kernel) (List.take_append_drop 3 leaf00935_w_source11)
    leaf00935_w_piece11_identity leaf00935_w_suffix12_eval leaf00935_w_suffix11_join x
#print axioms leaf00935_w_suffix11_join
#print axioms leaf00935_w_suffix11_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
