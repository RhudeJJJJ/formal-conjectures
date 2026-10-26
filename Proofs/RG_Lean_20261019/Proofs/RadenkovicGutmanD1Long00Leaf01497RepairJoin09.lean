/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01497RepairPiece09
import Proofs.RadenkovicGutmanD1Long00Leaf01497RepairJoin10
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01497_w_suffix09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01497_w_source10.length) leaf01497_w_piece09) leaf01497_w_suffix10)
theorem leaf01497_w_suffix09_join : leaf01497_w_suffix09=NestedInteger.add (NestedInteger.scale (64^leaf01497_w_source10.length) leaf01497_w_piece09) leaf01497_w_suffix10 := by decide +kernel
theorem leaf01497_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01497_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 27 leaf01497_w_source09)) x := by
  have hlen : leaf01497_w_segment09.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01497_w_source10.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 27 leaf01497_w_segment09)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 (27+leaf01497_w_segment09.length) leaf01497_w_source10)) x := by
      rw [leaf01497_w_suffix09_join,cast_add,eval_add,cast_scale,eval_scale,leaf01497_w_piece09_identity,leaf01497_w_suffix10_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 27 (leaf01497_w_segment09++leaf01497_w_source10))) x :=
      (IntegerOuterPieces.eval_append 12 1 64 27 leaf01497_w_segment09 leaf01497_w_source10 x).symm
    _ = _ := by rw [show leaf01497_w_segment09++leaf01497_w_source10=leaf01497_w_source09 from List.take_append_drop 3 leaf01497_w_source09]
#print axioms leaf01497_w_suffix09_join
#print axioms leaf01497_w_suffix09_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
