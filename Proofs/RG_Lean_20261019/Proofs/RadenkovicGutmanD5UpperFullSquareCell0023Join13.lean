/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece13
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join14
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source14.length) leaf00023_w_piece13) leaf00023_w_suffix14)
theorem leaf00023_w_suffix13_join : leaf00023_w_suffix13=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source14.length) leaf00023_w_piece13) leaf00023_w_suffix14 := by decide +kernel
theorem leaf00023_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 39 leaf00023_w_source13)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 39 42
    leaf00023_w_segment13 leaf00023_w_source14 leaf00023_w_source13
    leaf00023_w_piece13 leaf00023_w_suffix14 leaf00023_w_suffix13
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source13)
    leaf00023_w_piece13_identity leaf00023_w_suffix14_eval leaf00023_w_suffix13_join x
#print axioms leaf00023_w_suffix13_join
#print axioms leaf00023_w_suffix13_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
