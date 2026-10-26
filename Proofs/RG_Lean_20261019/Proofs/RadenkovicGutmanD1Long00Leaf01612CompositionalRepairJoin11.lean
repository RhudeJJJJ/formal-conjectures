/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairPiece11
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairJoin12
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01612_w_suffix11 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01612_w_source12.length) leaf01612_w_piece11) leaf01612_w_suffix12)
theorem leaf01612_w_suffix11_join : leaf01612_w_suffix11=NestedInteger.add (NestedInteger.scale (128^leaf01612_w_source12.length) leaf01612_w_piece11) leaf01612_w_suffix12 := by decide +kernel
theorem leaf01612_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01612_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 33 leaf01612_w_source11)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 33 36
    leaf01612_w_segment11 leaf01612_w_source12 leaf01612_w_source11
    leaf01612_w_piece11 leaf01612_w_suffix12 leaf01612_w_suffix11
    (by decide +kernel) (List.take_append_drop 3 leaf01612_w_source11)
    leaf01612_w_piece11_identity leaf01612_w_suffix12_eval leaf01612_w_suffix11_join x
#print axioms leaf01612_w_suffix11_join
#print axioms leaf01612_w_suffix11_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
