/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01258RepairPiece16
import Proofs.RadenkovicGutmanD1Long00Leaf01258RepairJoin17
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01258_w_suffix16 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01258_w_source17.length) leaf01258_w_piece16) leaf01258_w_suffix17)
theorem leaf01258_w_suffix16_join : leaf01258_w_suffix16=NestedInteger.add (NestedInteger.scale (16^leaf01258_w_source17.length) leaf01258_w_piece16) leaf01258_w_suffix17 := by decide +kernel
theorem leaf01258_w_suffix16_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01258_w_suffix16) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 leaf01258_w_source16)) x := by
  have hlen : leaf01258_w_segment16.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01258_w_source17.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 leaf01258_w_segment16)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (48+leaf01258_w_segment16.length) leaf01258_w_source17)) x := by
      rw [leaf01258_w_suffix16_join,cast_add,eval_add,cast_scale,eval_scale,leaf01258_w_piece16_identity,leaf01258_w_suffix17_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 (leaf01258_w_segment16++leaf01258_w_source17))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 48 leaf01258_w_segment16 leaf01258_w_source17 x).symm
    _ = _ := by rw [show leaf01258_w_segment16++leaf01258_w_source17=leaf01258_w_source16 from List.take_append_drop 3 leaf01258_w_source16]
#print axioms leaf01258_w_suffix16_join
#print axioms leaf01258_w_suffix16_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
