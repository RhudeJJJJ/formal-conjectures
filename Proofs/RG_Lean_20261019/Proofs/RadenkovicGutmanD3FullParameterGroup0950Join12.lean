/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Piece12
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Join13
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix12 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source13.length) leaf03800_w_piece12) leaf03800_w_suffix13)
theorem leaf03800_w_suffix12_join : leaf03800_w_suffix12=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source13.length) leaf03800_w_piece12) leaf03800_w_suffix13 := by decide +kernel
theorem leaf03800_w_suffix12_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix12) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 36 leaf03800_w_source12)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 36 39
    leaf03800_w_segment12 leaf03800_w_source13 leaf03800_w_source12
    leaf03800_w_piece12 leaf03800_w_suffix13 leaf03800_w_suffix12
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source12)
    leaf03800_w_piece12_identity leaf03800_w_suffix13_eval leaf03800_w_suffix12_join x
#print axioms leaf03800_w_suffix12_join
#print axioms leaf03800_w_suffix12_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
