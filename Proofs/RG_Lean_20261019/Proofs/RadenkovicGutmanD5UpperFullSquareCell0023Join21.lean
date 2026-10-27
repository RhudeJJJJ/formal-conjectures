/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece21
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join22
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix21 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source22.length) leaf00023_w_piece21) leaf00023_w_suffix22)
theorem leaf00023_w_suffix21_join : leaf00023_w_suffix21=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source22.length) leaf00023_w_piece21) leaf00023_w_suffix22 := by decide +kernel
theorem leaf00023_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 63 leaf00023_w_source21)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 63 66
    leaf00023_w_segment21 leaf00023_w_source22 leaf00023_w_source21
    leaf00023_w_piece21 leaf00023_w_suffix22 leaf00023_w_suffix21
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source21)
    leaf00023_w_piece21_identity leaf00023_w_suffix22_eval leaf00023_w_suffix21_join x
#print axioms leaf00023_w_suffix21_join
#print axioms leaf00023_w_suffix21_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
