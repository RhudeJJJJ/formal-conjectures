/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01445RepairPiece14
import Proofs.RadenkovicGutmanD1Long00Leaf01445RepairJoin15
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01445_w_suffix14 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01445_w_source15.length) leaf01445_w_piece14) leaf01445_w_suffix15)
theorem leaf01445_w_suffix14_join : leaf01445_w_suffix14=NestedInteger.add (NestedInteger.scale (64^leaf01445_w_source15.length) leaf01445_w_piece14) leaf01445_w_suffix15 := by decide +kernel
theorem leaf01445_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01445_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 15 1 64 42 leaf01445_w_source14)) x := by
  have hlen : leaf01445_w_segment14.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01445_w_source15.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 15 1 64 42 leaf01445_w_segment14)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 15 1 64 (42+leaf01445_w_segment14.length) leaf01445_w_source15)) x := by
      rw [leaf01445_w_suffix14_join,cast_add,eval_add,cast_scale,eval_scale,leaf01445_w_piece14_identity,leaf01445_w_suffix15_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 15 1 64 42 (leaf01445_w_segment14++leaf01445_w_source15))) x :=
      (IntegerOuterPieces.eval_append 15 1 64 42 leaf01445_w_segment14 leaf01445_w_source15 x).symm
    _ = _ := by rw [show leaf01445_w_segment14++leaf01445_w_source15=leaf01445_w_source14 from List.take_append_drop 3 leaf01445_w_source14]
#print axioms leaf01445_w_suffix14_join
#print axioms leaf01445_w_suffix14_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
