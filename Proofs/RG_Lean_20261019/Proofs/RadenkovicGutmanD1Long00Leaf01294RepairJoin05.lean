/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01294RepairPiece05
import Proofs.RadenkovicGutmanD1Long00Leaf01294RepairJoin06
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01294_w_suffix05 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01294_w_source06.length) leaf01294_w_piece05) leaf01294_w_suffix06)
theorem leaf01294_w_suffix05_join : leaf01294_w_suffix05=NestedInteger.add (NestedInteger.scale (32^leaf01294_w_source06.length) leaf01294_w_piece05) leaf01294_w_suffix06 := by decide +kernel
theorem leaf01294_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01294_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 15 leaf01294_w_source05)) x := by
  have hlen : leaf01294_w_segment05.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01294_w_source06.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 15 leaf01294_w_segment05)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (15+leaf01294_w_segment05.length) leaf01294_w_source06)) x := by
      rw [leaf01294_w_suffix05_join,cast_add,eval_add,cast_scale,eval_scale,leaf01294_w_piece05_identity,leaf01294_w_suffix06_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 15 (leaf01294_w_segment05++leaf01294_w_source06))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 15 leaf01294_w_segment05 leaf01294_w_source06 x).symm
    _ = _ := by rw [show leaf01294_w_segment05++leaf01294_w_source06=leaf01294_w_source05 from List.take_append_drop 3 leaf01294_w_source05]
#print axioms leaf01294_w_suffix05_join
#print axioms leaf01294_w_suffix05_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
