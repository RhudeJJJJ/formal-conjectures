/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01338RepairPiece20
import Proofs.RadenkovicGutmanD1Long00Leaf01338RepairJoin21
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01338_w_suffix20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01338_w_source21.length) leaf01338_w_piece20) leaf01338_w_suffix21)
theorem leaf01338_w_suffix20_join : leaf01338_w_suffix20=NestedInteger.add (NestedInteger.scale (32^leaf01338_w_source21.length) leaf01338_w_piece20) leaf01338_w_suffix21 := by decide +kernel
theorem leaf01338_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01338_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 60 leaf01338_w_source20)) x := by
  have hlen : leaf01338_w_segment20.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01338_w_source21.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 60 leaf01338_w_segment20)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 (60+leaf01338_w_segment20.length) leaf01338_w_source21)) x := by
      rw [leaf01338_w_suffix20_join,cast_add,eval_add,cast_scale,eval_scale,leaf01338_w_piece20_identity,leaf01338_w_suffix21_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 60 (leaf01338_w_segment20++leaf01338_w_source21))) x :=
      (IntegerOuterPieces.eval_append 12 1 32 60 leaf01338_w_segment20 leaf01338_w_source21 x).symm
    _ = _ := by rw [show leaf01338_w_segment20++leaf01338_w_source21=leaf01338_w_source20 from List.take_append_drop 3 leaf01338_w_source20]
#print axioms leaf01338_w_suffix20_join
#print axioms leaf01338_w_suffix20_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
