/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedPiece24
import Proofs.RadenkovicGutmanD1Long00Leaf01260FormulaJoin25
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix24 : NestedInteger.Poly 3 := (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source25.length) leaf01260_w_piece24) leaf01260_w_suffix25)
theorem leaf01260_w_suffix24_join : leaf01260_w_suffix24=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source25.length) leaf01260_w_piece24) leaf01260_w_suffix25 := by rfl
theorem leaf01260_w_suffix24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix24) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_source24)) x := by
  have hlen : leaf01260_w_segment24.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source25.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_segment24)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (72+leaf01260_w_segment24.length) leaf01260_w_source25)) x := by
      rw [leaf01260_w_suffix24_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece24_identity,leaf01260_w_suffix25_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 (leaf01260_w_segment24++leaf01260_w_source25))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 72 leaf01260_w_segment24 leaf01260_w_source25 x).symm
    _ = _ := by rw [show leaf01260_w_segment24++leaf01260_w_source25=leaf01260_w_source24 from List.take_append_drop 3 leaf01260_w_source24]
#print axioms leaf01260_w_suffix24_join
#print axioms leaf01260_w_suffix24_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
