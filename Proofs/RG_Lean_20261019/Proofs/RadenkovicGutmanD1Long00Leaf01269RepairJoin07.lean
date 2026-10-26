/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01269RepairPiece07
import Proofs.RadenkovicGutmanD1Long00Leaf01269RepairJoin08
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01269_w_suffix07 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01269_w_source08.length) leaf01269_w_piece07) leaf01269_w_suffix08)
theorem leaf01269_w_suffix07_join : leaf01269_w_suffix07=NestedInteger.add (NestedInteger.scale (16^leaf01269_w_source08.length) leaf01269_w_piece07) leaf01269_w_suffix08 := by decide +kernel
theorem leaf01269_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01269_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 leaf01269_w_source07)) x := by
  have hlen : leaf01269_w_segment07.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01269_w_source08.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 leaf01269_w_segment07)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (21+leaf01269_w_segment07.length) leaf01269_w_source08)) x := by
      rw [leaf01269_w_suffix07_join,cast_add,eval_add,cast_scale,eval_scale,leaf01269_w_piece07_identity,leaf01269_w_suffix08_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 (leaf01269_w_segment07++leaf01269_w_source08))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 21 leaf01269_w_segment07 leaf01269_w_source08 x).symm
    _ = _ := by rw [show leaf01269_w_segment07++leaf01269_w_source08=leaf01269_w_source07 from List.take_append_drop 3 leaf01269_w_source07]
#print axioms leaf01269_w_suffix07_join
#print axioms leaf01269_w_suffix07_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
