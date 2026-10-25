/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Piece28
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Join29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix28 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source29.length) leaf03800_w_piece28) leaf03800_w_suffix29)
theorem leaf03800_w_suffix28_join : leaf03800_w_suffix28=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source29.length) leaf03800_w_piece28) leaf03800_w_suffix29 := by decide +kernel
theorem leaf03800_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 84 leaf03800_w_source28)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 84 87
    leaf03800_w_segment28 leaf03800_w_source29 leaf03800_w_source28
    leaf03800_w_piece28 leaf03800_w_suffix29 leaf03800_w_suffix28
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source28)
    leaf03800_w_piece28_identity leaf03800_w_suffix29_eval leaf03800_w_suffix28_join x
#print axioms leaf03800_w_suffix28_join
#print axioms leaf03800_w_suffix28_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
