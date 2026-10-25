/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece10
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join11
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix10 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source11.length) leaf01900_w_piece10) leaf01900_w_suffix11)
theorem leaf01900_w_suffix10_join : leaf01900_w_suffix10=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source11.length) leaf01900_w_piece10) leaf01900_w_suffix11 := by decide +kernel
theorem leaf01900_w_suffix10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix10) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 30 leaf01900_w_source10)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 30 33
    leaf01900_w_segment10 leaf01900_w_source11 leaf01900_w_source10
    leaf01900_w_piece10 leaf01900_w_suffix11 leaf01900_w_suffix10
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source10)
    leaf01900_w_piece10_identity leaf01900_w_suffix11_eval leaf01900_w_suffix10_join x
#print axioms leaf01900_w_suffix10_join
#print axioms leaf01900_w_suffix10_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
