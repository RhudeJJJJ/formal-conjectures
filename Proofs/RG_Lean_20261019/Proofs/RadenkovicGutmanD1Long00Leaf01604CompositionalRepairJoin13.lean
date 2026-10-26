/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01604CompositionalRepairPiece13
import Proofs.RadenkovicGutmanD1Long00Leaf01604CompositionalRepairJoin14
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01604_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01604_w_source14.length) leaf01604_w_piece13) leaf01604_w_suffix14)
theorem leaf01604_w_suffix13_join : leaf01604_w_suffix13=NestedInteger.add (NestedInteger.scale (128^leaf01604_w_source14.length) leaf01604_w_piece13) leaf01604_w_suffix14 := by decide +kernel
theorem leaf01604_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01604_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 39 leaf01604_w_source13)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 39 42
    leaf01604_w_segment13 leaf01604_w_source14 leaf01604_w_source13
    leaf01604_w_piece13 leaf01604_w_suffix14 leaf01604_w_suffix13
    (by decide +kernel) (List.take_append_drop 3 leaf01604_w_source13)
    leaf01604_w_piece13_identity leaf01604_w_suffix14_eval leaf01604_w_suffix13_join x
#print axioms leaf01604_w_suffix13_join
#print axioms leaf01604_w_suffix13_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
