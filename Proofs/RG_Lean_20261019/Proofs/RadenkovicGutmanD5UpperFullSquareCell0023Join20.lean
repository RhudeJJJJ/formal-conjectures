/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece20
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join21
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source21.length) leaf00023_w_piece20) leaf00023_w_suffix21)
theorem leaf00023_w_suffix20_join : leaf00023_w_suffix20=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source21.length) leaf00023_w_piece20) leaf00023_w_suffix21 := by decide +kernel
theorem leaf00023_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 60 leaf00023_w_source20)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 60 63
    leaf00023_w_segment20 leaf00023_w_source21 leaf00023_w_source20
    leaf00023_w_piece20 leaf00023_w_suffix21 leaf00023_w_suffix20
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source20)
    leaf00023_w_piece20_identity leaf00023_w_suffix21_eval leaf00023_w_suffix20_join x
#print axioms leaf00023_w_suffix20_join
#print axioms leaf00023_w_suffix20_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
