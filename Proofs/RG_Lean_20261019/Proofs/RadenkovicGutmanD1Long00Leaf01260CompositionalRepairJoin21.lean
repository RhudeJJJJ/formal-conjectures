/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece21
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairJoin22
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix21 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22)
theorem leaf01260_w_suffix21_join : leaf01260_w_suffix21=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22 := by decide +kernel
theorem leaf01260_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_source21)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 63 66
    leaf01260_w_segment21 leaf01260_w_source22 leaf01260_w_source21
    leaf01260_w_piece21 leaf01260_w_suffix22 leaf01260_w_suffix21
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source21)
    leaf01260_w_piece21_identity leaf01260_w_suffix22_eval leaf01260_w_suffix21_join x
#print axioms leaf01260_w_suffix21_join
#print axioms leaf01260_w_suffix21_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
