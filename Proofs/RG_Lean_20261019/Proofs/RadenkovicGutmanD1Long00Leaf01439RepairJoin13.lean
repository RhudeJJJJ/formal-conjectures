/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01439RepairPiece13
import Proofs.RadenkovicGutmanD1Long00Leaf01439RepairJoin14
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01439_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01439_w_source14.length) leaf01439_w_piece13) leaf01439_w_suffix14)
theorem leaf01439_w_suffix13_join : leaf01439_w_suffix13=NestedInteger.add (NestedInteger.scale (64^leaf01439_w_source14.length) leaf01439_w_piece13) leaf01439_w_suffix14 := by decide +kernel
theorem leaf01439_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01439_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 39 leaf01439_w_source13)) x := by
  have hlen : leaf01439_w_segment13.length=3 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf01439_w_source14.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 39 leaf01439_w_segment13)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 (39+leaf01439_w_segment13.length) leaf01439_w_source14)) x := by
      rw [leaf01439_w_suffix13_join,cast_add,eval_add,cast_scale,eval_scale,leaf01439_w_piece13_identity,leaf01439_w_suffix14_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 16 1 64 39 (leaf01439_w_segment13++leaf01439_w_source14))) x :=
      (IntegerOuterPieces.eval_append 16 1 64 39 leaf01439_w_segment13 leaf01439_w_source14 x).symm
    _ = _ := by rw [show leaf01439_w_segment13++leaf01439_w_source14=leaf01439_w_source13 from List.take_append_drop 3 leaf01439_w_source13]
#print axioms leaf01439_w_suffix13_join
#print axioms leaf01439_w_suffix13_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
