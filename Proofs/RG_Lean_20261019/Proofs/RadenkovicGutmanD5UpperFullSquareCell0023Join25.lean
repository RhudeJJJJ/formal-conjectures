/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece25
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join26
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix25 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source26.length) leaf00023_w_piece25) leaf00023_w_suffix26)
theorem leaf00023_w_suffix25_join : leaf00023_w_suffix25=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source26.length) leaf00023_w_piece25) leaf00023_w_suffix26 := by decide +kernel
theorem leaf00023_w_suffix25_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix25) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 75 leaf00023_w_source25)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 75 78
    leaf00023_w_segment25 leaf00023_w_source26 leaf00023_w_source25
    leaf00023_w_piece25 leaf00023_w_suffix26 leaf00023_w_suffix25
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source25)
    leaf00023_w_piece25_identity leaf00023_w_suffix26_eval leaf00023_w_suffix25_join x
#print axioms leaf00023_w_suffix25_join
#print axioms leaf00023_w_suffix25_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
