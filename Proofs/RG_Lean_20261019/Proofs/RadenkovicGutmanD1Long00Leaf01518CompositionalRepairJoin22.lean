/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01518CompositionalRepairPiece22
import Proofs.RadenkovicGutmanD1Long00Leaf01518CompositionalRepairJoin23
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01518_w_suffix22 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01518_w_source23.length) leaf01518_w_piece22) leaf01518_w_suffix23)
theorem leaf01518_w_suffix22_join : leaf01518_w_suffix22=NestedInteger.add (NestedInteger.scale (64^leaf01518_w_source23.length) leaf01518_w_piece22) leaf01518_w_suffix23 := by decide +kernel
theorem leaf01518_w_suffix22_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01518_w_suffix22) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 64 66 leaf01518_w_source22)) x :=
  IntegerOuterJoinedEvaluation.joined 11 1 64 66 69
    leaf01518_w_segment22 leaf01518_w_source23 leaf01518_w_source22
    leaf01518_w_piece22 leaf01518_w_suffix23 leaf01518_w_suffix22
    (by decide +kernel) (List.take_append_drop 3 leaf01518_w_source22)
    leaf01518_w_piece22_identity leaf01518_w_suffix23_eval leaf01518_w_suffix22_join x
#print axioms leaf01518_w_suffix22_join
#print axioms leaf01518_w_suffix22_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
