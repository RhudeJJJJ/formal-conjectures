/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece09
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join10
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source10.length) leaf00023_w_piece09) leaf00023_w_suffix10)
theorem leaf00023_w_suffix09_join : leaf00023_w_suffix09=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source10.length) leaf00023_w_piece09) leaf00023_w_suffix10 := by decide +kernel
theorem leaf00023_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 27 leaf00023_w_source09)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 27 30
    leaf00023_w_segment09 leaf00023_w_source10 leaf00023_w_source09
    leaf00023_w_piece09 leaf00023_w_suffix10 leaf00023_w_suffix09
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source09)
    leaf00023_w_piece09_identity leaf00023_w_suffix10_eval leaf00023_w_suffix09_join x
#print axioms leaf00023_w_suffix09_join
#print axioms leaf00023_w_suffix09_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
