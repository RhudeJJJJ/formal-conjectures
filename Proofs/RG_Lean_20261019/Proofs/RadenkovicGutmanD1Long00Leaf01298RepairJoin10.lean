/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01298RepairPiece10
import Proofs.RadenkovicGutmanD1Long00Leaf01298RepairJoin11
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01298_w_suffix10 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01298_w_source11.length) leaf01298_w_piece10) leaf01298_w_suffix11)
theorem leaf01298_w_suffix10_join : leaf01298_w_suffix10=NestedInteger.add (NestedInteger.scale (32^leaf01298_w_source11.length) leaf01298_w_piece10) leaf01298_w_suffix11 := by decide +kernel
theorem leaf01298_w_suffix10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01298_w_suffix10) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 30 leaf01298_w_source10)) x := by
  have hlen : leaf01298_w_segment10.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01298_w_source11.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 30 leaf01298_w_segment10)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (30+leaf01298_w_segment10.length) leaf01298_w_source11)) x := by
      rw [leaf01298_w_suffix10_join,cast_add,eval_add,cast_scale,eval_scale,leaf01298_w_piece10_identity,leaf01298_w_suffix11_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 30 (leaf01298_w_segment10++leaf01298_w_source11))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 30 leaf01298_w_segment10 leaf01298_w_source11 x).symm
    _ = _ := by rw [show leaf01298_w_segment10++leaf01298_w_source11=leaf01298_w_source10 from List.take_append_drop 3 leaf01298_w_source10]
#print axioms leaf01298_w_suffix10_join
#print axioms leaf01298_w_suffix10_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
