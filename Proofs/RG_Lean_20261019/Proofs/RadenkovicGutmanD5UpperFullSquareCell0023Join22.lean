/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece22
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Join23
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix22 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source23.length) leaf00023_w_piece22) leaf00023_w_suffix23)
theorem leaf00023_w_suffix22_join : leaf00023_w_suffix22=NestedInteger.add (NestedInteger.scale (3200^leaf00023_w_source23.length) leaf00023_w_piece22) leaf00023_w_suffix23 := by decide +kernel
theorem leaf00023_w_suffix22_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix22) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 66 leaf00023_w_source22)) x :=
  IntegerOuterJoinedEvaluation.joined 27 1 3200 66 69
    leaf00023_w_segment22 leaf00023_w_source23 leaf00023_w_source22
    leaf00023_w_piece22 leaf00023_w_suffix23 leaf00023_w_suffix22
    (by decide +kernel) (List.take_append_drop 3 leaf00023_w_source22)
    leaf00023_w_piece22_identity leaf00023_w_suffix23_eval leaf00023_w_suffix22_join x
#print axioms leaf00023_w_suffix22_join
#print axioms leaf00023_w_suffix22_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
