/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01344RepairPiece25
import Proofs.RadenkovicGutmanD1Long00Leaf01344RepairJoin26
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01344_w_suffix25 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01344_w_source26.length) leaf01344_w_piece25) leaf01344_w_suffix26)
theorem leaf01344_w_suffix25_join : leaf01344_w_suffix25=NestedInteger.add (NestedInteger.scale (32^leaf01344_w_source26.length) leaf01344_w_piece25) leaf01344_w_suffix26 := by decide +kernel
theorem leaf01344_w_suffix25_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01344_w_suffix25) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 75 leaf01344_w_source25)) x := by
  have hlen : leaf01344_w_segment25.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01344_w_source26.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 75 leaf01344_w_segment25)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 (75+leaf01344_w_segment25.length) leaf01344_w_source26)) x := by
      rw [leaf01344_w_suffix25_join,cast_add,eval_add,cast_scale,eval_scale,leaf01344_w_piece25_identity,leaf01344_w_suffix26_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 75 (leaf01344_w_segment25++leaf01344_w_source26))) x :=
      (IntegerOuterPieces.eval_append 11 1 32 75 leaf01344_w_segment25 leaf01344_w_source26 x).symm
    _ = _ := by rw [show leaf01344_w_segment25++leaf01344_w_source26=leaf01344_w_source25 from List.take_append_drop 3 leaf01344_w_source25]
#print axioms leaf01344_w_suffix25_join
#print axioms leaf01344_w_suffix25_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
