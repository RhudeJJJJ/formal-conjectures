/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01618CompositionalRepairPiece26
import Proofs.RadenkovicGutmanD1Long00Leaf01618CompositionalRepairJoin27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01618_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01618_w_source27.length) leaf01618_w_piece26) leaf01618_w_suffix27)
theorem leaf01618_w_suffix26_join : leaf01618_w_suffix26=NestedInteger.add (NestedInteger.scale (128^leaf01618_w_source27.length) leaf01618_w_piece26) leaf01618_w_suffix27 := by decide +kernel
theorem leaf01618_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01618_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 15 1 128 78 leaf01618_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 15 1 128 78 81
    leaf01618_w_segment26 leaf01618_w_source27 leaf01618_w_source26
    leaf01618_w_piece26 leaf01618_w_suffix27 leaf01618_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf01618_w_source26)
    leaf01618_w_piece26_identity leaf01618_w_suffix27_eval leaf01618_w_suffix26_join x
#print axioms leaf01618_w_suffix26_join
#print axioms leaf01618_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
