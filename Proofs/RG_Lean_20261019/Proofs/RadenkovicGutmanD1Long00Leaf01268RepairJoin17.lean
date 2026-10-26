/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01268RepairPiece17
import Proofs.RadenkovicGutmanD1Long00Leaf01268RepairJoin18
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01268_w_suffix17 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01268_w_source18.length) leaf01268_w_piece17) leaf01268_w_suffix18)
theorem leaf01268_w_suffix17_join : leaf01268_w_suffix17=NestedInteger.add (NestedInteger.scale (16^leaf01268_w_source18.length) leaf01268_w_piece17) leaf01268_w_suffix18 := by decide +kernel
theorem leaf01268_w_suffix17_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01268_w_suffix17) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 leaf01268_w_source17)) x := by
  have hlen : leaf01268_w_segment17.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01268_w_source18.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 leaf01268_w_segment17)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (51+leaf01268_w_segment17.length) leaf01268_w_source18)) x := by
      rw [leaf01268_w_suffix17_join,cast_add,eval_add,cast_scale,eval_scale,leaf01268_w_piece17_identity,leaf01268_w_suffix18_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 (leaf01268_w_segment17++leaf01268_w_source18))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 51 leaf01268_w_segment17 leaf01268_w_source18 x).symm
    _ = _ := by rw [show leaf01268_w_segment17++leaf01268_w_source18=leaf01268_w_source17 from List.take_append_drop 3 leaf01268_w_source17]
#print axioms leaf01268_w_suffix17_join
#print axioms leaf01268_w_suffix17_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
