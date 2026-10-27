/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01402RepairPiece25
import Proofs.RadenkovicGutmanD1Long00Leaf01402RepairJoin26
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01402_w_suffix25 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01402_w_source26.length) leaf01402_w_piece25) leaf01402_w_suffix26)
theorem leaf01402_w_suffix25_join : leaf01402_w_suffix25=NestedInteger.add (NestedInteger.scale (64^leaf01402_w_source26.length) leaf01402_w_piece25) leaf01402_w_suffix26 := by decide +kernel
theorem leaf01402_w_suffix25_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01402_w_suffix25) x=eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 75 leaf01402_w_source25)) x := by
  have hlen : leaf01402_w_segment25.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01402_w_source26.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 75 leaf01402_w_segment25)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 (75+leaf01402_w_segment25.length) leaf01402_w_source26)) x := by
      rw [leaf01402_w_suffix25_join,cast_add,eval_add,cast_scale,eval_scale,leaf01402_w_piece25_identity,leaf01402_w_suffix26_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 75 (leaf01402_w_segment25++leaf01402_w_source26))) x :=
      (IntegerOuterPieces.eval_append 18 1 64 75 leaf01402_w_segment25 leaf01402_w_source26 x).symm
    _ = _ := by rw [show leaf01402_w_segment25++leaf01402_w_source26=leaf01402_w_source25 from List.take_append_drop 3 leaf01402_w_source25]
#print axioms leaf01402_w_suffix25_join
#print axioms leaf01402_w_suffix25_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
