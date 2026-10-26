/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01611CompositionalRepairPiece27
import Proofs.RadenkovicGutmanD1Long00Leaf01611CompositionalRepairJoin28
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01611_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01611_w_source28.length) leaf01611_w_piece27) leaf01611_w_suffix28)
theorem leaf01611_w_suffix27_join : leaf01611_w_suffix27=NestedInteger.add (NestedInteger.scale (128^leaf01611_w_source28.length) leaf01611_w_piece27) leaf01611_w_suffix28 := by decide +kernel
theorem leaf01611_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01611_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 81 leaf01611_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 81 84
    leaf01611_w_segment27 leaf01611_w_source28 leaf01611_w_source27
    leaf01611_w_piece27 leaf01611_w_suffix28 leaf01611_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf01611_w_source27)
    leaf01611_w_piece27_identity leaf01611_w_suffix28_eval leaf01611_w_suffix27_join x
#print axioms leaf01611_w_suffix27_join
#print axioms leaf01611_w_suffix27_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
