/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01519CompositionalRepairPiece01
import Proofs.RadenkovicGutmanD1Long00Leaf01519CompositionalRepairJoin02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01519_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01519_w_source02.length) leaf01519_w_piece01) leaf01519_w_suffix02)
theorem leaf01519_w_suffix01_join : leaf01519_w_suffix01=NestedInteger.add (NestedInteger.scale (64^leaf01519_w_source02.length) leaf01519_w_piece01) leaf01519_w_suffix02 := by decide +kernel
theorem leaf01519_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01519_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 64 3 leaf01519_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 11 1 64 3 6
    leaf01519_w_segment01 leaf01519_w_source02 leaf01519_w_source01
    leaf01519_w_piece01 leaf01519_w_suffix02 leaf01519_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf01519_w_source01)
    leaf01519_w_piece01_identity leaf01519_w_suffix02_eval leaf01519_w_suffix01_join x
#print axioms leaf01519_w_suffix01_join
#print axioms leaf01519_w_suffix01_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
