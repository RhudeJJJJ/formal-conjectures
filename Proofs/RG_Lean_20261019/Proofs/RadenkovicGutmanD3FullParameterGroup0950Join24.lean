/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Piece24
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Join25
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix24 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source25.length) leaf03800_w_piece24) leaf03800_w_suffix25)
theorem leaf03800_w_suffix24_join : leaf03800_w_suffix24=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source25.length) leaf03800_w_piece24) leaf03800_w_suffix25 := by decide +kernel
theorem leaf03800_w_suffix24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix24) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 72 leaf03800_w_source24)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 72 75
    leaf03800_w_segment24 leaf03800_w_source25 leaf03800_w_source24
    leaf03800_w_piece24 leaf03800_w_suffix25 leaf03800_w_suffix24
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source24)
    leaf03800_w_piece24_identity leaf03800_w_suffix25_eval leaf03800_w_suffix24_join x
#print axioms leaf03800_w_suffix24_join
#print axioms leaf03800_w_suffix24_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
