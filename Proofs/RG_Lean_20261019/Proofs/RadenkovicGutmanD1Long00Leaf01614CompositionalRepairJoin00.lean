/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01614CompositionalRepairPiece00
import Proofs.RadenkovicGutmanD1Long00Leaf01614CompositionalRepairJoin01
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01614_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01614_w_source01.length) leaf01614_w_piece00) leaf01614_w_suffix01)
theorem leaf01614_w_affine_join : leaf01614_w_affine=NestedInteger.add (NestedInteger.scale (128^leaf01614_w_source01.length) leaf01614_w_piece00) leaf01614_w_suffix01 := by decide +kernel
theorem leaf01614_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01614_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 16 1 128 0 leaf01614_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 16 1 128 0 3
    leaf01614_w_segment00 leaf01614_w_source01 leaf01614_w_source00
    leaf01614_w_piece00 leaf01614_w_suffix01 leaf01614_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf01614_w_source00)
    leaf01614_w_piece00_identity leaf01614_w_suffix01_eval leaf01614_w_affine_join x
#print axioms leaf01614_w_affine_join
#print axioms leaf01614_w_affine_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
