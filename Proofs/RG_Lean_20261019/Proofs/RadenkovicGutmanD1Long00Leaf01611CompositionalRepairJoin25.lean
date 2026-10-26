/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01611CompositionalRepairPiece25
import Proofs.RadenkovicGutmanD1Long00Leaf01611CompositionalRepairJoin26
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01611_w_suffix25 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01611_w_source26.length) leaf01611_w_piece25) leaf01611_w_suffix26)
theorem leaf01611_w_suffix25_join : leaf01611_w_suffix25=NestedInteger.add (NestedInteger.scale (128^leaf01611_w_source26.length) leaf01611_w_piece25) leaf01611_w_suffix26 := by decide +kernel
theorem leaf01611_w_suffix25_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01611_w_suffix25) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 75 leaf01611_w_source25)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 75 78
    leaf01611_w_segment25 leaf01611_w_source26 leaf01611_w_source25
    leaf01611_w_piece25 leaf01611_w_suffix26 leaf01611_w_suffix25
    (by decide +kernel) (List.take_append_drop 3 leaf01611_w_source25)
    leaf01611_w_piece25_identity leaf01611_w_suffix26_eval leaf01611_w_suffix25_join x
#print axioms leaf01611_w_suffix25_join
#print axioms leaf01611_w_suffix25_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
