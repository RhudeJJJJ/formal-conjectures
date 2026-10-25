/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01338RepairPiece21
import Proofs.RadenkovicGutmanD1Long00Leaf01338RepairJoin22
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01338_w_suffix21 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01338_w_source22.length) leaf01338_w_piece21) leaf01338_w_suffix22)
theorem leaf01338_w_suffix21_join : leaf01338_w_suffix21=NestedInteger.add (NestedInteger.scale (32^leaf01338_w_source22.length) leaf01338_w_piece21) leaf01338_w_suffix22 := by decide +kernel
theorem leaf01338_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01338_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 63 leaf01338_w_source21)) x := by
  have hlen : leaf01338_w_segment21.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01338_w_source22.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 63 leaf01338_w_segment21)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 (63+leaf01338_w_segment21.length) leaf01338_w_source22)) x := by
      rw [leaf01338_w_suffix21_join,cast_add,eval_add,cast_scale,eval_scale,leaf01338_w_piece21_identity,leaf01338_w_suffix22_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 63 (leaf01338_w_segment21++leaf01338_w_source22))) x :=
      (IntegerOuterPieces.eval_append 12 1 32 63 leaf01338_w_segment21 leaf01338_w_source22 x).symm
    _ = _ := by rw [show leaf01338_w_segment21++leaf01338_w_source22=leaf01338_w_source21 from List.take_append_drop 3 leaf01338_w_source21]
#print axioms leaf01338_w_suffix21_join
#print axioms leaf01338_w_suffix21_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
