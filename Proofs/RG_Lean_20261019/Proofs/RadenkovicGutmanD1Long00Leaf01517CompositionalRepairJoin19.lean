/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepairPiece19
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepairJoin20
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01517_w_suffix19 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01517_w_source20.length) leaf01517_w_piece19) leaf01517_w_suffix20)
theorem leaf01517_w_suffix19_join : leaf01517_w_suffix19=NestedInteger.add (NestedInteger.scale (64^leaf01517_w_source20.length) leaf01517_w_piece19) leaf01517_w_suffix20 := by decide +kernel
theorem leaf01517_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01517_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 64 57 leaf01517_w_source19)) x :=
  IntegerOuterJoinedEvaluation.joined 11 1 64 57 60
    leaf01517_w_segment19 leaf01517_w_source20 leaf01517_w_source19
    leaf01517_w_piece19 leaf01517_w_suffix20 leaf01517_w_suffix19
    (by decide +kernel) (List.take_append_drop 3 leaf01517_w_source19)
    leaf01517_w_piece19_identity leaf01517_w_suffix20_eval leaf01517_w_suffix19_join x
#print axioms leaf01517_w_suffix19_join
#print axioms leaf01517_w_suffix19_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
