/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01342RepairPiece04
import Proofs.RadenkovicGutmanD1Long00Leaf01342RepairJoin05
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01342_w_suffix04 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01342_w_source05.length) leaf01342_w_piece04) leaf01342_w_suffix05)
theorem leaf01342_w_suffix04_join : leaf01342_w_suffix04=NestedInteger.add (NestedInteger.scale (32^leaf01342_w_source05.length) leaf01342_w_piece04) leaf01342_w_suffix05 := by decide +kernel
theorem leaf01342_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01342_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 12 leaf01342_w_source04)) x := by
  have hlen : leaf01342_w_segment04.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01342_w_source05.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 12 leaf01342_w_segment04)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 (12+leaf01342_w_segment04.length) leaf01342_w_source05)) x := by
      rw [leaf01342_w_suffix04_join,cast_add,eval_add,cast_scale,eval_scale,leaf01342_w_piece04_identity,leaf01342_w_suffix05_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 12 (leaf01342_w_segment04++leaf01342_w_source05))) x :=
      (IntegerOuterPieces.eval_append 12 1 32 12 leaf01342_w_segment04 leaf01342_w_source05 x).symm
    _ = _ := by rw [show leaf01342_w_segment04++leaf01342_w_source05=leaf01342_w_source04 from List.take_append_drop 3 leaf01342_w_source04]
#print axioms leaf01342_w_suffix04_join
#print axioms leaf01342_w_suffix04_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
