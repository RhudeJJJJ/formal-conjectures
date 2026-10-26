/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01299RepairPiece12
import Proofs.RadenkovicGutmanD1Long00Leaf01299RepairJoin13
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01299_w_suffix12 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01299_w_source13.length) leaf01299_w_piece12) leaf01299_w_suffix13)
theorem leaf01299_w_suffix12_join : leaf01299_w_suffix12=NestedInteger.add (NestedInteger.scale (32^leaf01299_w_source13.length) leaf01299_w_piece12) leaf01299_w_suffix13 := by decide +kernel
theorem leaf01299_w_suffix12_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01299_w_suffix12) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 36 leaf01299_w_source12)) x := by
  have hlen : leaf01299_w_segment12.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01299_w_source13.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 36 leaf01299_w_segment12)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (36+leaf01299_w_segment12.length) leaf01299_w_source13)) x := by
      rw [leaf01299_w_suffix12_join,cast_add,eval_add,cast_scale,eval_scale,leaf01299_w_piece12_identity,leaf01299_w_suffix13_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 36 (leaf01299_w_segment12++leaf01299_w_source13))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 36 leaf01299_w_segment12 leaf01299_w_source13 x).symm
    _ = _ := by rw [show leaf01299_w_segment12++leaf01299_w_source13=leaf01299_w_source12 from List.take_append_drop 3 leaf01299_w_source12]
#print axioms leaf01299_w_suffix12_join
#print axioms leaf01299_w_suffix12_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
