/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01304RepairPiece27
import Proofs.RadenkovicGutmanD1Long00Leaf01304RepairJoin28
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01304_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01304_w_source28.length) leaf01304_w_piece27) leaf01304_w_suffix28)
theorem leaf01304_w_suffix27_join : leaf01304_w_suffix27=NestedInteger.add (NestedInteger.scale (32^leaf01304_w_source28.length) leaf01304_w_piece27) leaf01304_w_suffix28 := by decide +kernel
theorem leaf01304_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01304_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 81 leaf01304_w_source27)) x := by
  have hlen : leaf01304_w_segment27.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01304_w_source28.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 81 leaf01304_w_segment27)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (81+leaf01304_w_segment27.length) leaf01304_w_source28)) x := by
      rw [leaf01304_w_suffix27_join,cast_add,eval_add,cast_scale,eval_scale,leaf01304_w_piece27_identity,leaf01304_w_suffix28_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 81 (leaf01304_w_segment27++leaf01304_w_source28))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 81 leaf01304_w_segment27 leaf01304_w_source28 x).symm
    _ = _ := by rw [show leaf01304_w_segment27++leaf01304_w_source28=leaf01304_w_source27 from List.take_append_drop 3 leaf01304_w_source27]
#print axioms leaf01304_w_suffix27_join
#print axioms leaf01304_w_suffix27_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
