/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01300RepairPiece26
import Proofs.RadenkovicGutmanD1Long00Leaf01300RepairJoin27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01300_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01300_w_source27.length) leaf01300_w_piece26) leaf01300_w_suffix27)
theorem leaf01300_w_suffix26_join : leaf01300_w_suffix26=NestedInteger.add (NestedInteger.scale (32^leaf01300_w_source27.length) leaf01300_w_piece26) leaf01300_w_suffix27 := by decide +kernel
theorem leaf01300_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01300_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 78 leaf01300_w_source26)) x := by
  have hlen : leaf01300_w_segment26.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01300_w_source27.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 78 leaf01300_w_segment26)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (78+leaf01300_w_segment26.length) leaf01300_w_source27)) x := by
      rw [leaf01300_w_suffix26_join,cast_add,eval_add,cast_scale,eval_scale,leaf01300_w_piece26_identity,leaf01300_w_suffix27_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 78 (leaf01300_w_segment26++leaf01300_w_source27))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 78 leaf01300_w_segment26 leaf01300_w_source27 x).symm
    _ = _ := by rw [show leaf01300_w_segment26++leaf01300_w_source27=leaf01300_w_source26 from List.take_append_drop 3 leaf01300_w_source26]
#print axioms leaf01300_w_suffix26_join
#print axioms leaf01300_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
