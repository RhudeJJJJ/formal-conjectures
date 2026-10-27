/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece27
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join28
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source28.length) leaf00023_w_piece27) leaf00023_w_suffix28)
theorem leaf00023_w_suffix27_join : leaf00023_w_suffix27=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source28.length) leaf00023_w_piece27) leaf00023_w_suffix28 := by decide +kernel
theorem leaf00023_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 81 leaf00023_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 81 84
    leaf00023_w_segment27 leaf00023_w_source28 leaf00023_w_source27
    leaf00023_w_piece27 leaf00023_w_suffix28 leaf00023_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source27)
    leaf00023_w_piece27_identity leaf00023_w_suffix28_eval leaf00023_w_suffix27_join x
#print axioms leaf00023_w_suffix27_join
#print axioms leaf00023_w_suffix27_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
