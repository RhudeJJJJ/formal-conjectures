/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01431RepairPiece28
import Proofs.RadenkovicGutmanD1Long00Leaf01431RepairJoin29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01431_w_suffix28 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01431_w_source29.length) leaf01431_w_piece28) leaf01431_w_suffix29)
theorem leaf01431_w_suffix28_join : leaf01431_w_suffix28=NestedInteger.add (NestedInteger.scale (64^leaf01431_w_source29.length) leaf01431_w_piece28) leaf01431_w_suffix29 := by decide +kernel
theorem leaf01431_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01431_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 84 leaf01431_w_source28)) x := by
  have hlen : leaf01431_w_segment28.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01431_w_source29.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 84 leaf01431_w_segment28)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 (84+leaf01431_w_segment28.length) leaf01431_w_source29)) x := by
      rw [leaf01431_w_suffix28_join,cast_add,eval_add,cast_scale,eval_scale,leaf01431_w_piece28_identity,leaf01431_w_suffix29_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 84 (leaf01431_w_segment28++leaf01431_w_source29))) x :=
      (IntegerOuterPieces.eval_append 16 1 64 84 leaf01431_w_segment28 leaf01431_w_source29 x).symm
    _ = _ := by rw [show leaf01431_w_segment28++leaf01431_w_source29=leaf01431_w_source28 from List.take_append_drop 3 leaf01431_w_source28]
#print axioms leaf01431_w_suffix28_join
#print axioms leaf01431_w_suffix28_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
