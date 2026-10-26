/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01605CompositionalRepairPiece12
import Proofs.RadenkovicGutmanD1Long00Leaf01605CompositionalRepairJoin13
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01605_w_suffix12 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01605_w_source13.length) leaf01605_w_piece12) leaf01605_w_suffix13)
theorem leaf01605_w_suffix12_join : leaf01605_w_suffix12=NestedInteger.add (NestedInteger.scale (128^leaf01605_w_source13.length) leaf01605_w_piece12) leaf01605_w_suffix13 := by decide +kernel
theorem leaf01605_w_suffix12_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01605_w_suffix12) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 36 leaf01605_w_source12)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 36 39
    leaf01605_w_segment12 leaf01605_w_source13 leaf01605_w_source12
    leaf01605_w_piece12 leaf01605_w_suffix13 leaf01605_w_suffix12
    (by decide +kernel) (List.take_append_drop 3 leaf01605_w_source12)
    leaf01605_w_piece12_identity leaf01605_w_suffix13_eval leaf01605_w_suffix12_join x
#print axioms leaf01605_w_suffix12_join
#print axioms leaf01605_w_suffix12_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
