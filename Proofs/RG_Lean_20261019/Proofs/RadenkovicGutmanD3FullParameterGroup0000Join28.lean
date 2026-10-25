/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Piece28
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Join29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix28 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source29.length) leaf00000_w_piece28) leaf00000_w_suffix29)
theorem leaf00000_w_suffix28_join : leaf00000_w_suffix28=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source29.length) leaf00000_w_piece28) leaf00000_w_suffix29 := by decide +kernel
theorem leaf00000_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 84 leaf00000_w_source28)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 84 87
    leaf00000_w_segment28 leaf00000_w_source29 leaf00000_w_source28
    leaf00000_w_piece28 leaf00000_w_suffix29 leaf00000_w_suffix28
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source28)
    leaf00000_w_piece28_identity leaf00000_w_suffix29_eval leaf00000_w_suffix28_join x
#print axioms leaf00000_w_suffix28_join
#print axioms leaf00000_w_suffix28_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
