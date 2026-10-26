/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01330RepairPiece18
import Proofs.RadenkovicGutmanD1Long00Leaf01330RepairJoin19
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01330_w_suffix18 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01330_w_source19.length) leaf01330_w_piece18) leaf01330_w_suffix19)
theorem leaf01330_w_suffix18_join : leaf01330_w_suffix18=NestedInteger.add (NestedInteger.scale (32^leaf01330_w_source19.length) leaf01330_w_piece18) leaf01330_w_suffix19 := by decide +kernel
theorem leaf01330_w_suffix18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01330_w_suffix18) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 54 leaf01330_w_source18)) x := by
  have hlen : leaf01330_w_segment18.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01330_w_source19.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 54 leaf01330_w_segment18)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 (54+leaf01330_w_segment18.length) leaf01330_w_source19)) x := by
      rw [leaf01330_w_suffix18_join,cast_add,eval_add,cast_scale,eval_scale,leaf01330_w_piece18_identity,leaf01330_w_suffix19_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 54 (leaf01330_w_segment18++leaf01330_w_source19))) x :=
      (IntegerOuterPieces.eval_append 12 1 32 54 leaf01330_w_segment18 leaf01330_w_source19 x).symm
    _ = _ := by rw [show leaf01330_w_segment18++leaf01330_w_source19=leaf01330_w_source18 from List.take_append_drop 3 leaf01330_w_source18]
#print axioms leaf01330_w_suffix18_join
#print axioms leaf01330_w_suffix18_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
