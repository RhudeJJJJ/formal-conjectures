/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedPiece03
import Proofs.RadenkovicGutmanD1Long00Leaf01260FormulaJoin04
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix03 : NestedInteger.Poly 3 := (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source04.length) leaf01260_w_piece03) leaf01260_w_suffix04)
theorem leaf01260_w_suffix03_join : leaf01260_w_suffix03=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source04.length) leaf01260_w_piece03) leaf01260_w_suffix04 := by rfl
theorem leaf01260_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_source03)) x := by
  have hlen : leaf01260_w_segment03.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source04.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_segment03)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (9+leaf01260_w_segment03.length) leaf01260_w_source04)) x := by
      rw [leaf01260_w_suffix03_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece03_identity,leaf01260_w_suffix04_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 (leaf01260_w_segment03++leaf01260_w_source04))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 9 leaf01260_w_segment03 leaf01260_w_source04 x).symm
    _ = _ := by rw [show leaf01260_w_segment03++leaf01260_w_source04=leaf01260_w_source03 from List.take_append_drop 3 leaf01260_w_source03]
#print axioms leaf01260_w_suffix03_join
#print axioms leaf01260_w_suffix03_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
