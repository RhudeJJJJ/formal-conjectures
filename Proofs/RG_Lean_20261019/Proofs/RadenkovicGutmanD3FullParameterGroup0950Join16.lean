/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Piece16
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Join17
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix16 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source17.length) leaf03800_w_piece16) leaf03800_w_suffix17)
theorem leaf03800_w_suffix16_join : leaf03800_w_suffix16=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source17.length) leaf03800_w_piece16) leaf03800_w_suffix17 := by decide +kernel
theorem leaf03800_w_suffix16_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix16) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 48 leaf03800_w_source16)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 48 51
    leaf03800_w_segment16 leaf03800_w_source17 leaf03800_w_source16
    leaf03800_w_piece16 leaf03800_w_suffix17 leaf03800_w_suffix16
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source16)
    leaf03800_w_piece16_identity leaf03800_w_suffix17_eval leaf03800_w_suffix16_join x
#print axioms leaf03800_w_suffix16_join
#print axioms leaf03800_w_suffix16_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
