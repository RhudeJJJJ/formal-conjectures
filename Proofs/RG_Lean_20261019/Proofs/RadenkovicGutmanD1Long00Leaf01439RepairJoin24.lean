/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01439RepairPiece24
import Proofs.RadenkovicGutmanD1Long00Leaf01439RepairJoin25
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01439_w_suffix24 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01439_w_source25.length) leaf01439_w_piece24) leaf01439_w_suffix25)
theorem leaf01439_w_suffix24_join : leaf01439_w_suffix24=NestedInteger.add (NestedInteger.scale (64^leaf01439_w_source25.length) leaf01439_w_piece24) leaf01439_w_suffix25 := by decide +kernel
theorem leaf01439_w_suffix24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01439_w_suffix24) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 72 leaf01439_w_source24)) x := by
  have hlen : leaf01439_w_segment24.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01439_w_source25.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 72 leaf01439_w_segment24)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 (72+leaf01439_w_segment24.length) leaf01439_w_source25)) x := by
      rw [leaf01439_w_suffix24_join,cast_add,eval_add,cast_scale,eval_scale,leaf01439_w_piece24_identity,leaf01439_w_suffix25_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 72 (leaf01439_w_segment24++leaf01439_w_source25))) x :=
      (IntegerOuterPieces.eval_append 16 1 64 72 leaf01439_w_segment24 leaf01439_w_source25 x).symm
    _ = _ := by rw [show leaf01439_w_segment24++leaf01439_w_source25=leaf01439_w_source24 from List.take_append_drop 3 leaf01439_w_source24]
#print axioms leaf01439_w_suffix24_join
#print axioms leaf01439_w_suffix24_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
