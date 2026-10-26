/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01264RepairPiece14
import Proofs.RadenkovicGutmanD1Long00Leaf01264RepairJoin15
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01264_w_suffix14 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01264_w_source15.length) leaf01264_w_piece14) leaf01264_w_suffix15)
theorem leaf01264_w_suffix14_join : leaf01264_w_suffix14=NestedInteger.add (NestedInteger.scale (16^leaf01264_w_source15.length) leaf01264_w_piece14) leaf01264_w_suffix15 := by decide +kernel
theorem leaf01264_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01264_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 leaf01264_w_source14)) x := by
  have hlen : leaf01264_w_segment14.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01264_w_source15.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 leaf01264_w_segment14)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (42+leaf01264_w_segment14.length) leaf01264_w_source15)) x := by
      rw [leaf01264_w_suffix14_join,cast_add,eval_add,cast_scale,eval_scale,leaf01264_w_piece14_identity,leaf01264_w_suffix15_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 (leaf01264_w_segment14++leaf01264_w_source15))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 42 leaf01264_w_segment14 leaf01264_w_source15 x).symm
    _ = _ := by rw [show leaf01264_w_segment14++leaf01264_w_source15=leaf01264_w_source14 from List.take_append_drop 3 leaf01264_w_source14]
#print axioms leaf01264_w_suffix14_join
#print axioms leaf01264_w_suffix14_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
