/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01346RepairPiece11
import Proofs.RadenkovicGutmanD1Long00Leaf01346RepairJoin12
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01346_w_suffix11 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01346_w_source12.length) leaf01346_w_piece11) leaf01346_w_suffix12)
theorem leaf01346_w_suffix11_join : leaf01346_w_suffix11=NestedInteger.add (NestedInteger.scale (32^leaf01346_w_source12.length) leaf01346_w_piece11) leaf01346_w_suffix12 := by decide +kernel
theorem leaf01346_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01346_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 33 leaf01346_w_source11)) x := by
  have hlen : leaf01346_w_segment11.length=3 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01346_w_source12.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 33 leaf01346_w_segment11)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 (33+leaf01346_w_segment11.length) leaf01346_w_source12)) x := by
      rw [leaf01346_w_suffix11_join,cast_add,eval_add,cast_scale,eval_scale,leaf01346_w_piece11_identity,leaf01346_w_suffix12_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 11 1 32 33 (leaf01346_w_segment11++leaf01346_w_source12))) x :=
      (IntegerOuterPieces.eval_append 11 1 32 33 leaf01346_w_segment11 leaf01346_w_source12 x).symm
    _ = _ := by rw [show leaf01346_w_segment11++leaf01346_w_source12=leaf01346_w_source11 from List.take_append_drop 3 leaf01346_w_source11]
#print axioms leaf01346_w_suffix11_join
#print axioms leaf01346_w_suffix11_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
