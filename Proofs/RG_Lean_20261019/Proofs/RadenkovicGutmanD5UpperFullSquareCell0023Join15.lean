/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece15
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join16
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix15 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source16.length) leaf00023_w_piece15) leaf00023_w_suffix16)
theorem leaf00023_w_suffix15_join : leaf00023_w_suffix15=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source16.length) leaf00023_w_piece15) leaf00023_w_suffix16 := by decide +kernel
theorem leaf00023_w_suffix15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix15) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 45 leaf00023_w_source15)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 45 48
    leaf00023_w_segment15 leaf00023_w_source16 leaf00023_w_source15
    leaf00023_w_piece15 leaf00023_w_suffix16 leaf00023_w_suffix15
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source15)
    leaf00023_w_piece15_identity leaf00023_w_suffix16_eval leaf00023_w_suffix15_join x
#print axioms leaf00023_w_suffix15_join
#print axioms leaf00023_w_suffix15_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
