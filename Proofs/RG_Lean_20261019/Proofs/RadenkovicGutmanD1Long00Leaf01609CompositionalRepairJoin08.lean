/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01609CompositionalRepairPiece08
import Proofs.RadenkovicGutmanD1Long00Leaf01609CompositionalRepairJoin09
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01609_w_suffix08 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01609_w_source09.length) leaf01609_w_piece08) leaf01609_w_suffix09)
theorem leaf01609_w_suffix08_join : leaf01609_w_suffix08=NestedInteger.add (NestedInteger.scale (128^leaf01609_w_source09.length) leaf01609_w_piece08) leaf01609_w_suffix09 := by decide +kernel
theorem leaf01609_w_suffix08_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01609_w_suffix08) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 24 leaf01609_w_source08)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 24 27
    leaf01609_w_segment08 leaf01609_w_source09 leaf01609_w_source08
    leaf01609_w_piece08 leaf01609_w_suffix09 leaf01609_w_suffix08
    (by decide +kernel) (List.take_append_drop 3 leaf01609_w_source08)
    leaf01609_w_piece08_identity leaf01609_w_suffix09_eval leaf01609_w_suffix08_join x
#print axioms leaf01609_w_suffix08_join
#print axioms leaf01609_w_suffix08_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
