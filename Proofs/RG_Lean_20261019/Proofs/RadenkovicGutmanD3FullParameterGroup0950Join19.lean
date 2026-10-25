/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Piece19
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Join20
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix19 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source20.length) leaf03800_w_piece19) leaf03800_w_suffix20)
theorem leaf03800_w_suffix19_join : leaf03800_w_suffix19=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source20.length) leaf03800_w_piece19) leaf03800_w_suffix20 := by decide +kernel
theorem leaf03800_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 57 leaf03800_w_source19)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 57 60
    leaf03800_w_segment19 leaf03800_w_source20 leaf03800_w_source19
    leaf03800_w_piece19 leaf03800_w_suffix20 leaf03800_w_suffix19
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source19)
    leaf03800_w_piece19_identity leaf03800_w_suffix20_eval leaf03800_w_suffix19_join x
#print axioms leaf03800_w_suffix19_join
#print axioms leaf03800_w_suffix19_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
