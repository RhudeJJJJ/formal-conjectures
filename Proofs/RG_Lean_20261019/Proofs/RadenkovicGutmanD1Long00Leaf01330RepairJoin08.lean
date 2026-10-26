/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01330RepairPiece08
import Proofs.RadenkovicGutmanD1Long00Leaf01330RepairJoin09
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01330_w_suffix08 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01330_w_source09.length) leaf01330_w_piece08) leaf01330_w_suffix09)
theorem leaf01330_w_suffix08_join : leaf01330_w_suffix08=NestedInteger.add (NestedInteger.scale (32^leaf01330_w_source09.length) leaf01330_w_piece08) leaf01330_w_suffix09 := by decide +kernel
theorem leaf01330_w_suffix08_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01330_w_suffix08) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 24 leaf01330_w_source08)) x := by
  have hlen : leaf01330_w_segment08.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01330_w_source09.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 24 leaf01330_w_segment08)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 (24+leaf01330_w_segment08.length) leaf01330_w_source09)) x := by
      rw [leaf01330_w_suffix08_join,cast_add,eval_add,cast_scale,eval_scale,leaf01330_w_piece08_identity,leaf01330_w_suffix09_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 32 24 (leaf01330_w_segment08++leaf01330_w_source09))) x :=
      (IntegerOuterPieces.eval_append 12 1 32 24 leaf01330_w_segment08 leaf01330_w_source09 x).symm
    _ = _ := by rw [show leaf01330_w_segment08++leaf01330_w_source09=leaf01330_w_source08 from List.take_append_drop 3 leaf01330_w_source08]
#print axioms leaf01330_w_suffix08_join
#print axioms leaf01330_w_suffix08_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
