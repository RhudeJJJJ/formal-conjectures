/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01307RepairPiece02
import Proofs.RadenkovicGutmanD1Long00Leaf01307RepairJoin03
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01307_w_suffix02 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01307_w_source03.length) leaf01307_w_piece02) leaf01307_w_suffix03)
theorem leaf01307_w_suffix02_join : leaf01307_w_suffix02=NestedInteger.add (NestedInteger.scale (32^leaf01307_w_source03.length) leaf01307_w_piece02) leaf01307_w_suffix03 := by decide +kernel
theorem leaf01307_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01307_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 6 leaf01307_w_source02)) x := by
  have hlen : leaf01307_w_segment02.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01307_w_source03.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 6 leaf01307_w_segment02)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 (6+leaf01307_w_segment02.length) leaf01307_w_source03)) x := by
      rw [leaf01307_w_suffix02_join,cast_add,eval_add,cast_scale,eval_scale,leaf01307_w_piece02_identity,leaf01307_w_suffix03_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 32 6 (leaf01307_w_segment02++leaf01307_w_source03))) x :=
      (IntegerOuterPieces.eval_append 14 1 32 6 leaf01307_w_segment02 leaf01307_w_source03 x).symm
    _ = _ := by rw [show leaf01307_w_segment02++leaf01307_w_source03=leaf01307_w_source02 from List.take_append_drop 3 leaf01307_w_source02]
#print axioms leaf01307_w_suffix02_join
#print axioms leaf01307_w_suffix02_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
