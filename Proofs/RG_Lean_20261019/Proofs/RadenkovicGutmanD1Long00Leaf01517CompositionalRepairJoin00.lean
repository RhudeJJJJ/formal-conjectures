/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepairPiece00
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepairJoin01
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01517_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf01517_w_source01.length) leaf01517_w_piece00) leaf01517_w_suffix01)
theorem leaf01517_w_affine_join : leaf01517_w_affine=NestedInteger.add (NestedInteger.scale (64^leaf01517_w_source01.length) leaf01517_w_piece00) leaf01517_w_suffix01 := by decide +kernel
theorem leaf01517_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01517_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 11 1 64 0 leaf01517_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 11 1 64 0 3
    leaf01517_w_segment00 leaf01517_w_source01 leaf01517_w_source00
    leaf01517_w_piece00 leaf01517_w_suffix01 leaf01517_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf01517_w_source00)
    leaf01517_w_piece00_identity leaf01517_w_suffix01_eval leaf01517_w_affine_join x
#print axioms leaf01517_w_affine_join
#print axioms leaf01517_w_affine_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
