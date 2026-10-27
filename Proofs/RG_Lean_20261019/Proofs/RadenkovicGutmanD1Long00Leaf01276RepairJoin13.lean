/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01276RepairPiece13
import Proofs.RadenkovicGutmanD1Long00Leaf01276RepairJoin14
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01276_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01276_w_source14.length) leaf01276_w_piece13) leaf01276_w_suffix14)
theorem leaf01276_w_suffix13_join : leaf01276_w_suffix13=NestedInteger.add (NestedInteger.scale (32^leaf01276_w_source14.length) leaf01276_w_piece13) leaf01276_w_suffix14 := by decide +kernel
theorem leaf01276_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01276_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 39 leaf01276_w_source13)) x := by
  have hlen : leaf01276_w_segment13.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01276_w_source14.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 39 leaf01276_w_segment13)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 (39+leaf01276_w_segment13.length) leaf01276_w_source14)) x := by
      rw [leaf01276_w_suffix13_join,cast_add,eval_add,cast_scale,eval_scale,leaf01276_w_piece13_identity,leaf01276_w_suffix14_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 15 1 32 39 (leaf01276_w_segment13++leaf01276_w_source14))) x :=
      (IntegerOuterPieces.eval_append 15 1 32 39 leaf01276_w_segment13 leaf01276_w_source14 x).symm
    _ = _ := by rw [show leaf01276_w_segment13++leaf01276_w_source14=leaf01276_w_source13 from List.take_append_drop 3 leaf01276_w_source13]
#print axioms leaf01276_w_suffix13_join
#print axioms leaf01276_w_suffix13_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
