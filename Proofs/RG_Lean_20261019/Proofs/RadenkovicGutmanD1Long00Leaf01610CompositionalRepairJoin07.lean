/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01610CompositionalRepairPiece07
import Proofs.RadenkovicGutmanD1Long00Leaf01610CompositionalRepairJoin08
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01610_w_suffix07 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01610_w_source08.length) leaf01610_w_piece07) leaf01610_w_suffix08)
theorem leaf01610_w_suffix07_join : leaf01610_w_suffix07=NestedInteger.add (NestedInteger.scale (128^leaf01610_w_source08.length) leaf01610_w_piece07) leaf01610_w_suffix08 := by decide +kernel
theorem leaf01610_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01610_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 21 leaf01610_w_source07)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 21 24
    leaf01610_w_segment07 leaf01610_w_source08 leaf01610_w_source07
    leaf01610_w_piece07 leaf01610_w_suffix08 leaf01610_w_suffix07
    (by decide +kernel) (List.take_append_drop 3 leaf01610_w_source07)
    leaf01610_w_piece07_identity leaf01610_w_suffix08_eval leaf01610_w_suffix07_join x
#print axioms leaf01610_w_suffix07_join
#print axioms leaf01610_w_suffix07_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
