/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01614CompositionalRepairPiece03
import Proofs.RadenkovicGutmanD1Long00Leaf01614CompositionalRepairJoin04
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01614_w_suffix03 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01614_w_source04.length) leaf01614_w_piece03) leaf01614_w_suffix04)
theorem leaf01614_w_suffix03_join : leaf01614_w_suffix03=NestedInteger.add (NestedInteger.scale (128^leaf01614_w_source04.length) leaf01614_w_piece03) leaf01614_w_suffix04 := by decide +kernel
theorem leaf01614_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01614_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 9 leaf01614_w_source03)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 9 12
    leaf01614_w_segment03 leaf01614_w_source04 leaf01614_w_source03
    leaf01614_w_piece03 leaf01614_w_suffix04 leaf01614_w_suffix03
    (by decide +kernel) (List.take_append_drop 3 leaf01614_w_source03)
    leaf01614_w_piece03_identity leaf01614_w_suffix04_eval leaf01614_w_suffix03_join x
#print axioms leaf01614_w_suffix03_join
#print axioms leaf01614_w_suffix03_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
