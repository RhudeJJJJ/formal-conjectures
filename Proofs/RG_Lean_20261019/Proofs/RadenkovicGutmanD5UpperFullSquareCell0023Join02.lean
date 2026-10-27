/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece02
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join03
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix02 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source03.length) leaf00023_w_piece02) leaf00023_w_suffix03)
theorem leaf00023_w_suffix02_join : leaf00023_w_suffix02=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source03.length) leaf00023_w_piece02) leaf00023_w_suffix03 := by decide +kernel
theorem leaf00023_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 6 leaf00023_w_source02)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 6 9
    leaf00023_w_segment02 leaf00023_w_source03 leaf00023_w_source02
    leaf00023_w_piece02 leaf00023_w_suffix03 leaf00023_w_suffix02
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source02)
    leaf00023_w_piece02_identity leaf00023_w_suffix03_eval leaf00023_w_suffix02_join x
#print axioms leaf00023_w_suffix02_join
#print axioms leaf00023_w_suffix02_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
