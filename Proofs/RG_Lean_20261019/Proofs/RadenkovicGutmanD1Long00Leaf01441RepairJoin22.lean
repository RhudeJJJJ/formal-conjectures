/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01441RepairPiece22
import Proofs.RadenkovicGutmanD1Long00Leaf01441RepairJoin23
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01441_w_suffix22 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01441_w_source23.length) leaf01441_w_piece22) leaf01441_w_suffix23)
theorem leaf01441_w_suffix22_join : leaf01441_w_suffix22=NestedInteger.add (NestedInteger.scale (64^leaf01441_w_source23.length) leaf01441_w_piece22) leaf01441_w_suffix23 := by decide +kernel
theorem leaf01441_w_suffix22_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01441_w_suffix22) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 66 leaf01441_w_source22)) x := by
  have hlen : leaf01441_w_segment22.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01441_w_source23.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 66 leaf01441_w_segment22)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 (66+leaf01441_w_segment22.length) leaf01441_w_source23)) x := by
      rw [leaf01441_w_suffix22_join,cast_add,eval_add,cast_scale,eval_scale,leaf01441_w_piece22_identity,leaf01441_w_suffix23_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 66 (leaf01441_w_segment22++leaf01441_w_source23))) x :=
      (IntegerOuterPieces.eval_append 16 1 64 66 leaf01441_w_segment22 leaf01441_w_source23 x).symm
    _ = _ := by rw [show leaf01441_w_segment22++leaf01441_w_source23=leaf01441_w_source22 from List.take_append_drop 3 leaf01441_w_source22]
#print axioms leaf01441_w_suffix22_join
#print axioms leaf01441_w_suffix22_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
