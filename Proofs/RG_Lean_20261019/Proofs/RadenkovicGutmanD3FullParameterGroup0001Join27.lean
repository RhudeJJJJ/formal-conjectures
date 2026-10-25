/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Piece27
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Join28
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00004_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source28.length) leaf00004_w_piece27) leaf00004_w_suffix28)
theorem leaf00004_w_suffix27_join : leaf00004_w_suffix27=NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source28.length) leaf00004_w_piece27) leaf00004_w_suffix28 := by decide +kernel
theorem leaf00004_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00004_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 81 leaf00004_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 81 84
    leaf00004_w_segment27 leaf00004_w_source28 leaf00004_w_source27
    leaf00004_w_piece27 leaf00004_w_suffix28 leaf00004_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf00004_w_source27)
    leaf00004_w_piece27_identity leaf00004_w_suffix28_eval leaf00004_w_suffix27_join x
#print axioms leaf00004_w_suffix27_join
#print axioms leaf00004_w_suffix27_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
