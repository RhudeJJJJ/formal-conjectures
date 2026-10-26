/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01619CompositionalRepairPiece04
import Proofs.RadenkovicGutmanD1Long00Leaf01619CompositionalRepairJoin05
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01619_w_suffix04 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01619_w_source05.length) leaf01619_w_piece04) leaf01619_w_suffix05)
theorem leaf01619_w_suffix04_join : leaf01619_w_suffix04=NestedInteger.add (NestedInteger.scale (128^leaf01619_w_source05.length) leaf01619_w_piece04) leaf01619_w_suffix05 := by decide +kernel
theorem leaf01619_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01619_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 15 1 128 12 leaf01619_w_source04)) x :=
  IntegerOuterJoinedEvaluation.joined 15 1 128 12 15
    leaf01619_w_segment04 leaf01619_w_source05 leaf01619_w_source04
    leaf01619_w_piece04 leaf01619_w_suffix05 leaf01619_w_suffix04
    (by decide +kernel) (List.take_append_drop 3 leaf01619_w_source04)
    leaf01619_w_piece04_identity leaf01619_w_suffix05_eval leaf01619_w_suffix04_join x
#print axioms leaf01619_w_suffix04_join
#print axioms leaf01619_w_suffix04_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
