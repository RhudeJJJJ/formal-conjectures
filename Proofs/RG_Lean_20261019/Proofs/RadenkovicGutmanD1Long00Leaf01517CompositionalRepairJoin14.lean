/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepairPiece14
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepairJoin15
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01517_w_suffix14 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01517_w_source15.length) leaf01517_w_piece14) leaf01517_w_suffix15)
theorem leaf01517_w_suffix14_join : leaf01517_w_suffix14=NestedInteger.add (NestedInteger.scale (64^leaf01517_w_source15.length) leaf01517_w_piece14) leaf01517_w_suffix15 := by decide +kernel
theorem leaf01517_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01517_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 64 42 leaf01517_w_source14)) x :=
  IntegerOuterJoinedEvaluation.joined 11 1 64 42 45
    leaf01517_w_segment14 leaf01517_w_source15 leaf01517_w_source14
    leaf01517_w_piece14 leaf01517_w_suffix15 leaf01517_w_suffix14
    (by decide +kernel) (List.take_append_drop 3 leaf01517_w_source14)
    leaf01517_w_piece14_identity leaf01517_w_suffix15_eval leaf01517_w_suffix14_join x
#print axioms leaf01517_w_suffix14_join
#print axioms leaf01517_w_suffix14_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
