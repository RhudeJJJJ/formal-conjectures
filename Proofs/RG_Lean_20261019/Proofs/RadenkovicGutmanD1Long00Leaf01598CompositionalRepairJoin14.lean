/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01598CompositionalRepairPiece14
import Proofs.RadenkovicGutmanD1Long00Leaf01598CompositionalRepairJoin15
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01598_w_suffix14 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01598_w_source15.length) leaf01598_w_piece14) leaf01598_w_suffix15)
theorem leaf01598_w_suffix14_join : leaf01598_w_suffix14=NestedInteger.add (NestedInteger.scale (128^leaf01598_w_source15.length) leaf01598_w_piece14) leaf01598_w_suffix15 := by decide +kernel
theorem leaf01598_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01598_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 42 leaf01598_w_source14)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 42 45
    leaf01598_w_segment14 leaf01598_w_source15 leaf01598_w_source14
    leaf01598_w_piece14 leaf01598_w_suffix15 leaf01598_w_suffix14
    (by decide +kernel) (List.take_append_drop 3 leaf01598_w_source14)
    leaf01598_w_piece14_identity leaf01598_w_suffix15_eval leaf01598_w_suffix14_join x
#print axioms leaf01598_w_suffix14_join
#print axioms leaf01598_w_suffix14_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
