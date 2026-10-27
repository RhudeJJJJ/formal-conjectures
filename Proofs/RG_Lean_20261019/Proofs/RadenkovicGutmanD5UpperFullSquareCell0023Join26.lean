/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece26
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source27.length) leaf00023_w_piece26) leaf00023_w_suffix27)
theorem leaf00023_w_suffix26_join : leaf00023_w_suffix26=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source27.length) leaf00023_w_piece26) leaf00023_w_suffix27 := by decide +kernel
theorem leaf00023_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 78 leaf00023_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 78 81
    leaf00023_w_segment26 leaf00023_w_source27 leaf00023_w_source26
    leaf00023_w_piece26 leaf00023_w_suffix27 leaf00023_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source26)
    leaf00023_w_piece26_identity leaf00023_w_suffix27_eval leaf00023_w_suffix26_join x
#print axioms leaf00023_w_suffix26_join
#print axioms leaf00023_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
