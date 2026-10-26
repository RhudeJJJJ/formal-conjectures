/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01679CompositionalRepairPiece19
import Proofs.RadenkovicGutmanD1Long00Leaf01679CompositionalRepairJoin20
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01679_w_suffix19 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01679_w_source20.length) leaf01679_w_piece19) leaf01679_w_suffix20)
theorem leaf01679_w_suffix19_join : leaf01679_w_suffix19=NestedInteger.add (NestedInteger.scale (128^leaf01679_w_source20.length) leaf01679_w_piece19) leaf01679_w_suffix20 := by decide +kernel
theorem leaf01679_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01679_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 57 leaf01679_w_source19)) x :=
  IntegerOuterJoinedEvaluation.joined 12 1 128 57 60
    leaf01679_w_segment19 leaf01679_w_source20 leaf01679_w_source19
    leaf01679_w_piece19 leaf01679_w_suffix20 leaf01679_w_suffix19
    (by decide +kernel) (List.take_append_drop 3 leaf01679_w_source19)
    leaf01679_w_piece19_identity leaf01679_w_suffix20_eval leaf01679_w_suffix19_join x
#print axioms leaf01679_w_suffix19_join
#print axioms leaf01679_w_suffix19_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
