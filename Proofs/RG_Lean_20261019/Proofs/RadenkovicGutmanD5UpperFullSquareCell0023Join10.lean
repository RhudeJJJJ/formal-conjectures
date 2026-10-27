/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece10
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join11
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix10 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source11.length) leaf00023_w_piece10) leaf00023_w_suffix11)
theorem leaf00023_w_suffix10_join : leaf00023_w_suffix10=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source11.length) leaf00023_w_piece10) leaf00023_w_suffix11 := by decide +kernel
theorem leaf00023_w_suffix10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix10) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 30 leaf00023_w_source10)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 30 33
    leaf00023_w_segment10 leaf00023_w_source11 leaf00023_w_source10
    leaf00023_w_piece10 leaf00023_w_suffix11 leaf00023_w_suffix10
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source10)
    leaf00023_w_piece10_identity leaf00023_w_suffix11_eval leaf00023_w_suffix10_join x
#print axioms leaf00023_w_suffix10_join
#print axioms leaf00023_w_suffix10_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
