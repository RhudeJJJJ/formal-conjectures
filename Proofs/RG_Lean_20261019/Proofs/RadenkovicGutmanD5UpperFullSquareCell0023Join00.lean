/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece00
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join01
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source01.length) leaf00023_w_piece00) leaf00023_w_suffix01)
theorem leaf00023_w_affine_join : leaf00023_w_affine=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source01.length) leaf00023_w_piece00) leaf00023_w_suffix01 := by decide +kernel
theorem leaf00023_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 0 leaf00023_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 0 3
    leaf00023_w_segment00 leaf00023_w_source01 leaf00023_w_source00
    leaf00023_w_piece00 leaf00023_w_suffix01 leaf00023_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source00)
    leaf00023_w_piece00_identity leaf00023_w_suffix01_eval leaf00023_w_affine_join x
#print axioms leaf00023_w_affine_join
#print axioms leaf00023_w_affine_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
