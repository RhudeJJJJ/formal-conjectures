/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedPiece21
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedJoin22
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_suffix21 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22)
theorem leaf01260_w_suffix21_join : leaf01260_w_suffix21=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22 := by decide +kernel
theorem leaf01260_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_source21)) x := by
  have hlen : leaf01260_w_segment21.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source22.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_segment21)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (63+leaf01260_w_segment21.length) leaf01260_w_source22)) x := by
      rw [leaf01260_w_suffix21_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece21_identity,leaf01260_w_suffix22_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 (leaf01260_w_segment21++leaf01260_w_source22))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 63 leaf01260_w_segment21 leaf01260_w_source22 x).symm
    _ = _ := by rw [show leaf01260_w_segment21++leaf01260_w_source22=leaf01260_w_source21 from List.take_append_drop 3 leaf01260_w_source21]
#print axioms leaf01260_w_suffix21_join
#print axioms leaf01260_w_suffix21_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
