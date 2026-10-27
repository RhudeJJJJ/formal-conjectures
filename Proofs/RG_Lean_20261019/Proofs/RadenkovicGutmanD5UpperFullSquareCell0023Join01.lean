/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece01
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source02.length) leaf00023_w_piece01) leaf00023_w_suffix02)
theorem leaf00023_w_suffix01_join : leaf00023_w_suffix01=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source02.length) leaf00023_w_piece01) leaf00023_w_suffix02 := by decide +kernel
theorem leaf00023_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 3 leaf00023_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 3 6
    leaf00023_w_segment01 leaf00023_w_source02 leaf00023_w_source01
    leaf00023_w_piece01 leaf00023_w_suffix02 leaf00023_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source01)
    leaf00023_w_piece01_identity leaf00023_w_suffix02_eval leaf00023_w_suffix01_join x
#print axioms leaf00023_w_suffix01_join
#print axioms leaf00023_w_suffix01_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
