/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01302RepairPiece06
import Proofs.RadenkovicGutmanD1Long00Leaf01302RepairJoin07
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01302_w_suffix06 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01302_w_source07.length) leaf01302_w_piece06) leaf01302_w_suffix07)
theorem leaf01302_w_suffix06_join : leaf01302_w_suffix06=NestedInteger.add (NestedInteger.scale (32^leaf01302_w_source07.length) leaf01302_w_piece06) leaf01302_w_suffix07 := by decide +kernel
theorem leaf01302_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01302_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 18 leaf01302_w_source06)) x := by
  have hlen : leaf01302_w_segment06.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01302_w_source07.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 18 leaf01302_w_segment06)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (18+leaf01302_w_segment06.length) leaf01302_w_source07)) x := by
      rw [leaf01302_w_suffix06_join,cast_add,eval_add,cast_scale,eval_scale,leaf01302_w_piece06_identity,leaf01302_w_suffix07_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 18 (leaf01302_w_segment06++leaf01302_w_source07))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 18 leaf01302_w_segment06 leaf01302_w_source07 x).symm
    _ = _ := by rw [show leaf01302_w_segment06++leaf01302_w_source07=leaf01302_w_source06 from List.take_append_drop 3 leaf01302_w_source06]
#print axioms leaf01302_w_suffix06_join
#print axioms leaf01302_w_suffix06_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
