/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01346RepairPiece07
import Proofs.RadenkovicGutmanD1Long00Leaf01346RepairJoin08
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01346_w_suffix07 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01346_w_source08.length) leaf01346_w_piece07) leaf01346_w_suffix08)
theorem leaf01346_w_suffix07_join : leaf01346_w_suffix07=NestedInteger.add (NestedInteger.scale (32^leaf01346_w_source08.length) leaf01346_w_piece07) leaf01346_w_suffix08 := by decide +kernel
theorem leaf01346_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01346_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 21 leaf01346_w_source07)) x := by
  have hlen : leaf01346_w_segment07.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01346_w_source08.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 21 leaf01346_w_segment07)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 (21+leaf01346_w_segment07.length) leaf01346_w_source08)) x := by
      rw [leaf01346_w_suffix07_join,cast_add,eval_add,cast_scale,eval_scale,leaf01346_w_piece07_identity,leaf01346_w_suffix08_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 21 (leaf01346_w_segment07++leaf01346_w_source08))) x :=
      (IntegerOuterPieces.eval_append 11 1 32 21 leaf01346_w_segment07 leaf01346_w_source08 x).symm
    _ = _ := by rw [show leaf01346_w_segment07++leaf01346_w_source08=leaf01346_w_source07 from List.take_append_drop 3 leaf01346_w_source07]
#print axioms leaf01346_w_suffix07_join
#print axioms leaf01346_w_suffix07_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
