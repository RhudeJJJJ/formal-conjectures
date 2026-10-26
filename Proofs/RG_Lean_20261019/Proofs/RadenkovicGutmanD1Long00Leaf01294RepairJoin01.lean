/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01294RepairPiece01
import Proofs.RadenkovicGutmanD1Long00Leaf01294RepairJoin02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01294_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01294_w_source02.length) leaf01294_w_piece01) leaf01294_w_suffix02)
theorem leaf01294_w_suffix01_join : leaf01294_w_suffix01=NestedInteger.add (NestedInteger.scale (32^leaf01294_w_source02.length) leaf01294_w_piece01) leaf01294_w_suffix02 := by decide +kernel
theorem leaf01294_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01294_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 3 leaf01294_w_source01)) x := by
  have hlen : leaf01294_w_segment01.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01294_w_source02.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 3 leaf01294_w_segment01)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (3+leaf01294_w_segment01.length) leaf01294_w_source02)) x := by
      rw [leaf01294_w_suffix01_join,cast_add,eval_add,cast_scale,eval_scale,leaf01294_w_piece01_identity,leaf01294_w_suffix02_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 3 (leaf01294_w_segment01++leaf01294_w_source02))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 3 leaf01294_w_segment01 leaf01294_w_source02 x).symm
    _ = _ := by rw [show leaf01294_w_segment01++leaf01294_w_source02=leaf01294_w_source01 from List.take_append_drop 3 leaf01294_w_source01]
#print axioms leaf01294_w_suffix01_join
#print axioms leaf01294_w_suffix01_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
