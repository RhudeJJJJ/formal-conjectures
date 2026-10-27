/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece07
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join08
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix07 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source08.length) leaf00023_w_piece07) leaf00023_w_suffix08)
theorem leaf00023_w_suffix07_join : leaf00023_w_suffix07=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source08.length) leaf00023_w_piece07) leaf00023_w_suffix08 := by decide +kernel
theorem leaf00023_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 21 leaf00023_w_source07)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 21 24
    leaf00023_w_segment07 leaf00023_w_source08 leaf00023_w_source07
    leaf00023_w_piece07 leaf00023_w_suffix08 leaf00023_w_suffix07
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source07)
    leaf00023_w_piece07_identity leaf00023_w_suffix08_eval leaf00023_w_suffix07_join x
#print axioms leaf00023_w_suffix07_join
#print axioms leaf00023_w_suffix07_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
