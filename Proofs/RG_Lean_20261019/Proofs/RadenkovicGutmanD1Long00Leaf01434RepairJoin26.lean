/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01434RepairPiece26
import Proofs.RadenkovicGutmanD1Long00Leaf01434RepairJoin27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01434_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01434_w_source27.length) leaf01434_w_piece26) leaf01434_w_suffix27)
theorem leaf01434_w_suffix26_join : leaf01434_w_suffix26=NestedInteger.add (NestedInteger.scale (64^leaf01434_w_source27.length) leaf01434_w_piece26) leaf01434_w_suffix27 := by decide +kernel
theorem leaf01434_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01434_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 78 leaf01434_w_source26)) x := by
  have hlen : leaf01434_w_segment26.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01434_w_source27.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 78 leaf01434_w_segment26)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 (78+leaf01434_w_segment26.length) leaf01434_w_source27)) x := by
      rw [leaf01434_w_suffix26_join,cast_add,eval_add,cast_scale,eval_scale,leaf01434_w_piece26_identity,leaf01434_w_suffix27_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 78 (leaf01434_w_segment26++leaf01434_w_source27))) x :=
      (IntegerOuterPieces.eval_append 16 1 64 78 leaf01434_w_segment26 leaf01434_w_source27 x).symm
    _ = _ := by rw [show leaf01434_w_segment26++leaf01434_w_source27=leaf01434_w_source26 from List.take_append_drop 3 leaf01434_w_source26]
#print axioms leaf01434_w_suffix26_join
#print axioms leaf01434_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
