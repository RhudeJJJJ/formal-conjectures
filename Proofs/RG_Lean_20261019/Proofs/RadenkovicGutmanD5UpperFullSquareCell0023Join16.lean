/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece16
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join17
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix16 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source17.length) leaf00023_w_piece16) leaf00023_w_suffix17)
theorem leaf00023_w_suffix16_join : leaf00023_w_suffix16=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source17.length) leaf00023_w_piece16) leaf00023_w_suffix17 := by decide +kernel
theorem leaf00023_w_suffix16_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix16) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 48 leaf00023_w_source16)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 48 51
    leaf00023_w_segment16 leaf00023_w_source17 leaf00023_w_source16
    leaf00023_w_piece16 leaf00023_w_suffix17 leaf00023_w_suffix16
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source16)
    leaf00023_w_piece16_identity leaf00023_w_suffix17_eval leaf00023_w_suffix16_join x
#print axioms leaf00023_w_suffix16_join
#print axioms leaf00023_w_suffix16_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
