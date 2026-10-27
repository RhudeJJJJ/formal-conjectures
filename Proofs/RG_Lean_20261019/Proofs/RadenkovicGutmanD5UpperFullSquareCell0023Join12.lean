/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece12
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join13
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix12 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source13.length) leaf00023_w_piece12) leaf00023_w_suffix13)
theorem leaf00023_w_suffix12_join : leaf00023_w_suffix12=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source13.length) leaf00023_w_piece12) leaf00023_w_suffix13 := by decide +kernel
theorem leaf00023_w_suffix12_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix12) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 36 leaf00023_w_source12)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 36 39
    leaf00023_w_segment12 leaf00023_w_source13 leaf00023_w_source12
    leaf00023_w_piece12 leaf00023_w_suffix13 leaf00023_w_suffix12
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source12)
    leaf00023_w_piece12_identity leaf00023_w_suffix13_eval leaf00023_w_suffix12_join x
#print axioms leaf00023_w_suffix12_join
#print axioms leaf00023_w_suffix12_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
