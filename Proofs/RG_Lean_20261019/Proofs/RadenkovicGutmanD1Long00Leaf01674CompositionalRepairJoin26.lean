/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01674CompositionalRepairPiece26
import Proofs.RadenkovicGutmanD1Long00Leaf01674CompositionalRepairJoin27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01674_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01674_w_source27.length) leaf01674_w_piece26) leaf01674_w_suffix27)
theorem leaf01674_w_suffix26_join : leaf01674_w_suffix26=NestedInteger.add (NestedInteger.scale (128^leaf01674_w_source27.length) leaf01674_w_piece26) leaf01674_w_suffix27 := by decide +kernel
theorem leaf01674_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01674_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 78 leaf01674_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 12 1 128 78 81
    leaf01674_w_segment26 leaf01674_w_source27 leaf01674_w_source26
    leaf01674_w_piece26 leaf01674_w_suffix27 leaf01674_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf01674_w_source26)
    leaf01674_w_piece26_identity leaf01674_w_suffix27_eval leaf01674_w_suffix26_join x
#print axioms leaf01674_w_suffix26_join
#print axioms leaf01674_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
