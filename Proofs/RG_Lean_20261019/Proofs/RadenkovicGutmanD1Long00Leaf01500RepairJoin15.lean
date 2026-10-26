/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01500RepairPiece15
import Proofs.RadenkovicGutmanD1Long00Leaf01500RepairJoin16
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01500_w_suffix15 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01500_w_source16.length) leaf01500_w_piece15) leaf01500_w_suffix16)
theorem leaf01500_w_suffix15_join : leaf01500_w_suffix15=NestedInteger.add (NestedInteger.scale (64^leaf01500_w_source16.length) leaf01500_w_piece15) leaf01500_w_suffix16 := by decide +kernel
theorem leaf01500_w_suffix15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01500_w_suffix15) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 45 leaf01500_w_source15)) x := by
  have hlen : leaf01500_w_segment15.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01500_w_source16.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 45 leaf01500_w_segment15)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 (45+leaf01500_w_segment15.length) leaf01500_w_source16)) x := by
      rw [leaf01500_w_suffix15_join,cast_add,eval_add,cast_scale,eval_scale,leaf01500_w_piece15_identity,leaf01500_w_suffix16_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 64 45 (leaf01500_w_segment15++leaf01500_w_source16))) x :=
      (IntegerOuterPieces.eval_append 12 1 64 45 leaf01500_w_segment15 leaf01500_w_source16 x).symm
    _ = _ := by rw [show leaf01500_w_segment15++leaf01500_w_source16=leaf01500_w_source15 from List.take_append_drop 3 leaf01500_w_source15]
#print axioms leaf01500_w_suffix15_join
#print axioms leaf01500_w_suffix15_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
