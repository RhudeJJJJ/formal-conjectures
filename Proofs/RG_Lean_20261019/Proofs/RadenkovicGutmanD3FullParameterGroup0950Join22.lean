/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Piece22
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Join23
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix22 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source23.length) leaf03800_w_piece22) leaf03800_w_suffix23)
theorem leaf03800_w_suffix22_join : leaf03800_w_suffix22=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source23.length) leaf03800_w_piece22) leaf03800_w_suffix23 := by decide +kernel
theorem leaf03800_w_suffix22_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix22) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 66 leaf03800_w_source22)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 66 69
    leaf03800_w_segment22 leaf03800_w_source23 leaf03800_w_source22
    leaf03800_w_piece22 leaf03800_w_suffix23 leaf03800_w_suffix22
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source22)
    leaf03800_w_piece22_identity leaf03800_w_suffix23_eval leaf03800_w_suffix22_join x
#print axioms leaf03800_w_suffix22_join
#print axioms leaf03800_w_suffix22_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
