/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece28
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairJoin29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix28 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source29.length) leaf01260_w_piece28) leaf01260_w_suffix29)
theorem leaf01260_w_suffix28_join : leaf01260_w_suffix28=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source29.length) leaf01260_w_piece28) leaf01260_w_suffix29 := by decide +kernel
theorem leaf01260_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_source28)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 84 87
    leaf01260_w_segment28 leaf01260_w_source29 leaf01260_w_source28
    leaf01260_w_piece28 leaf01260_w_suffix29 leaf01260_w_suffix28
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source28)
    leaf01260_w_piece28_identity leaf01260_w_suffix29_eval leaf01260_w_suffix28_join x
#print axioms leaf01260_w_suffix28_join
#print axioms leaf01260_w_suffix28_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
