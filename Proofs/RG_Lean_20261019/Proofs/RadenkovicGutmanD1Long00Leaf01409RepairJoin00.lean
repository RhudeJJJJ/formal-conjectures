/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01409RepairPiece00
import Proofs.RadenkovicGutmanD1Long00Leaf01409RepairJoin01
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01409_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01409_w_source01.length) leaf01409_w_piece00) leaf01409_w_suffix01)
theorem leaf01409_w_affine_join : leaf01409_w_affine=NestedInteger.add (NestedInteger.scale (64^leaf01409_w_source01.length) leaf01409_w_piece00) leaf01409_w_suffix01 := by decide +kernel
theorem leaf01409_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01409_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 0 leaf01409_w_source00)) x := by
  have hlen : leaf01409_w_segment00.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01409_w_source01.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 0 leaf01409_w_segment00)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 (0+leaf01409_w_segment00.length) leaf01409_w_source01)) x := by
      rw [leaf01409_w_affine_join,cast_add,eval_add,cast_scale,eval_scale,leaf01409_w_piece00_identity,leaf01409_w_suffix01_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 18 1 64 0 (leaf01409_w_segment00++leaf01409_w_source01))) x :=
      (IntegerOuterPieces.eval_append 18 1 64 0 leaf01409_w_segment00 leaf01409_w_source01 x).symm
    _ = _ := by rw [show leaf01409_w_segment00++leaf01409_w_source01=leaf01409_w_source00 from List.take_append_drop 3 leaf01409_w_source00]
#print axioms leaf01409_w_affine_join
#print axioms leaf01409_w_affine_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
