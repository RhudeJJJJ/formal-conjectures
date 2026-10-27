/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01276RepairPiece19
import Proofs.RadenkovicGutmanD1Long00Leaf01276RepairJoin20
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01276_w_suffix19 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01276_w_source20.length) leaf01276_w_piece19) leaf01276_w_suffix20)
theorem leaf01276_w_suffix19_join : leaf01276_w_suffix19=NestedInteger.add (NestedInteger.scale (32^leaf01276_w_source20.length) leaf01276_w_piece19) leaf01276_w_suffix20 := by decide +kernel
theorem leaf01276_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01276_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 57 leaf01276_w_source19)) x := by
  have hlen : leaf01276_w_segment19.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01276_w_source20.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 57 leaf01276_w_segment19)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 (57+leaf01276_w_segment19.length) leaf01276_w_source20)) x := by
      rw [leaf01276_w_suffix19_join,cast_add,eval_add,cast_scale,eval_scale,leaf01276_w_piece19_identity,leaf01276_w_suffix20_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 57 (leaf01276_w_segment19++leaf01276_w_source20))) x :=
      (IntegerOuterPieces.eval_append 15 1 32 57 leaf01276_w_segment19 leaf01276_w_source20 x).symm
    _ = _ := by rw [show leaf01276_w_segment19++leaf01276_w_source20=leaf01276_w_source19 from List.take_append_drop 3 leaf01276_w_source19]
#print axioms leaf01276_w_suffix19_join
#print axioms leaf01276_w_suffix19_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
