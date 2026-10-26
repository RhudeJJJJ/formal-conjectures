/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01677CompositionalRepairPiece24
import Proofs.RadenkovicGutmanD1Long00Leaf01677CompositionalRepairJoin25
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01677_w_suffix24 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01677_w_source25.length) leaf01677_w_piece24) leaf01677_w_suffix25)
theorem leaf01677_w_suffix24_join : leaf01677_w_suffix24=NestedInteger.add (NestedInteger.scale (128^leaf01677_w_source25.length) leaf01677_w_piece24) leaf01677_w_suffix25 := by decide +kernel
theorem leaf01677_w_suffix24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01677_w_suffix24) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 72 leaf01677_w_source24)) x :=
  IntegerOuterJoinedEvaluation.joined 12 1 128 72 75
    leaf01677_w_segment24 leaf01677_w_source25 leaf01677_w_source24
    leaf01677_w_piece24 leaf01677_w_suffix25 leaf01677_w_suffix24
    (by decide +kernel) (List.take_append_drop 3 leaf01677_w_source24)
    leaf01677_w_piece24_identity leaf01677_w_suffix25_eval leaf01677_w_suffix24_join x
#print axioms leaf01677_w_suffix24_join
#print axioms leaf01677_w_suffix24_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
