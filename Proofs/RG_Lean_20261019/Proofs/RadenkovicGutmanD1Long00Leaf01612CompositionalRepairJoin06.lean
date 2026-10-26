/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairPiece06
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairJoin07
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01612_w_suffix06 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01612_w_source07.length) leaf01612_w_piece06) leaf01612_w_suffix07)
theorem leaf01612_w_suffix06_join : leaf01612_w_suffix06=NestedInteger.add (NestedInteger.scale (128^leaf01612_w_source07.length) leaf01612_w_piece06) leaf01612_w_suffix07 := by decide +kernel
theorem leaf01612_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01612_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 18 leaf01612_w_source06)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 18 21
    leaf01612_w_segment06 leaf01612_w_source07 leaf01612_w_source06
    leaf01612_w_piece06 leaf01612_w_suffix07 leaf01612_w_suffix06
    (by decide +kernel) (List.take_append_drop 3 leaf01612_w_source06)
    leaf01612_w_piece06_identity leaf01612_w_suffix07_eval leaf01612_w_suffix06_join x
#print axioms leaf01612_w_suffix06_join
#print axioms leaf01612_w_suffix06_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
