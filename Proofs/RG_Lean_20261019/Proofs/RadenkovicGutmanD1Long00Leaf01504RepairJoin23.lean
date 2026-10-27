/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01504RepairPiece23
import Proofs.RadenkovicGutmanD1Long00Leaf01504RepairJoin24
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01504_w_suffix23 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01504_w_source24.length) leaf01504_w_piece23) leaf01504_w_suffix24)
theorem leaf01504_w_suffix23_join : leaf01504_w_suffix23=NestedInteger.add (NestedInteger.scale (64^leaf01504_w_source24.length) leaf01504_w_piece23) leaf01504_w_suffix24 := by decide +kernel
theorem leaf01504_w_suffix23_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01504_w_suffix23) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 69 leaf01504_w_source23)) x := by
  have hlen : leaf01504_w_segment23.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01504_w_source24.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 69 leaf01504_w_segment23)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 (69+leaf01504_w_segment23.length) leaf01504_w_source24)) x := by
      rw [leaf01504_w_suffix23_join,cast_add,eval_add,cast_scale,eval_scale,leaf01504_w_piece23_identity,leaf01504_w_suffix24_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 69 (leaf01504_w_segment23++leaf01504_w_source24))) x :=
      (IntegerOuterPieces.eval_append 12 1 64 69 leaf01504_w_segment23 leaf01504_w_source24 x).symm
    _ = _ := by rw [show leaf01504_w_segment23++leaf01504_w_source24=leaf01504_w_source23 from List.take_append_drop 3 leaf01504_w_source23]
#print axioms leaf01504_w_suffix23_join
#print axioms leaf01504_w_suffix23_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
