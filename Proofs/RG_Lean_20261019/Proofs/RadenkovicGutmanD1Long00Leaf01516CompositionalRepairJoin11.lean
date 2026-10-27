/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01516CompositionalRepairPiece11
import Proofs.RadenkovicGutmanD1Long00Leaf01516CompositionalRepairJoin12
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01516_w_suffix11 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01516_w_source12.length) leaf01516_w_piece11) leaf01516_w_suffix12)
theorem leaf01516_w_suffix11_join : leaf01516_w_suffix11=NestedInteger.add (NestedInteger.scale (64^leaf01516_w_source12.length) leaf01516_w_piece11) leaf01516_w_suffix12 := by decide +kernel
theorem leaf01516_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01516_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 64 33 leaf01516_w_source11)) x :=
  IntegerOuterJoinedEvaluation.joined 11 1 64 33 36
    leaf01516_w_segment11 leaf01516_w_source12 leaf01516_w_source11
    leaf01516_w_piece11 leaf01516_w_suffix12 leaf01516_w_suffix11
    (by decide +kernel) (List.take_append_drop 3 leaf01516_w_source11)
    leaf01516_w_piece11_identity leaf01516_w_suffix12_eval leaf01516_w_suffix11_join x
#print axioms leaf01516_w_suffix11_join
#print axioms leaf01516_w_suffix11_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
