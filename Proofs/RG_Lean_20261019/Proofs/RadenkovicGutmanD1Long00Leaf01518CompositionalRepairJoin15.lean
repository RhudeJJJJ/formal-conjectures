/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01518CompositionalRepairPiece15
import Proofs.RadenkovicGutmanD1Long00Leaf01518CompositionalRepairJoin16
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01518_w_suffix15 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01518_w_source16.length) leaf01518_w_piece15) leaf01518_w_suffix16)
theorem leaf01518_w_suffix15_join : leaf01518_w_suffix15=NestedInteger.add (NestedInteger.scale (64^leaf01518_w_source16.length) leaf01518_w_piece15) leaf01518_w_suffix16 := by decide +kernel
theorem leaf01518_w_suffix15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01518_w_suffix15) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 64 45 leaf01518_w_source15)) x :=
  IntegerOuterJoinedEvaluation.joined 11 1 64 45 48
    leaf01518_w_segment15 leaf01518_w_source16 leaf01518_w_source15
    leaf01518_w_piece15 leaf01518_w_suffix16 leaf01518_w_suffix15
    (by decide +kernel) (List.take_append_drop 3 leaf01518_w_source15)
    leaf01518_w_piece15_identity leaf01518_w_suffix16_eval leaf01518_w_suffix15_join x
#print axioms leaf01518_w_suffix15_join
#print axioms leaf01518_w_suffix15_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
