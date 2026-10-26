/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairPiece10
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairJoin11
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01612_w_suffix10 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01612_w_source11.length) leaf01612_w_piece10) leaf01612_w_suffix11)
theorem leaf01612_w_suffix10_join : leaf01612_w_suffix10=NestedInteger.add (NestedInteger.scale (128^leaf01612_w_source11.length) leaf01612_w_piece10) leaf01612_w_suffix11 := by decide +kernel
theorem leaf01612_w_suffix10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01612_w_suffix10) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 30 leaf01612_w_source10)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 30 33
    leaf01612_w_segment10 leaf01612_w_source11 leaf01612_w_source10
    leaf01612_w_piece10 leaf01612_w_suffix11 leaf01612_w_suffix10
    (by decide +kernel) (List.take_append_drop 3 leaf01612_w_source10)
    leaf01612_w_piece10_identity leaf01612_w_suffix11_eval leaf01612_w_suffix10_join x
#print axioms leaf01612_w_suffix10_join
#print axioms leaf01612_w_suffix10_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
