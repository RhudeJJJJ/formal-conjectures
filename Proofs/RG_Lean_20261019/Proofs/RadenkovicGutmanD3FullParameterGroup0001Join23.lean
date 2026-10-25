/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Piece23
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Join24
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00004_w_suffix23 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source24.length) leaf00004_w_piece23) leaf00004_w_suffix24)
theorem leaf00004_w_suffix23_join : leaf00004_w_suffix23=NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source24.length) leaf00004_w_piece23) leaf00004_w_suffix24 := by decide +kernel
theorem leaf00004_w_suffix23_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00004_w_suffix23) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 69 leaf00004_w_source23)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 69 72
    leaf00004_w_segment23 leaf00004_w_source24 leaf00004_w_source23
    leaf00004_w_piece23 leaf00004_w_suffix24 leaf00004_w_suffix23
    (by decide +kernel) (List.take_append_drop 3 leaf00004_w_source23)
    leaf00004_w_piece23_identity leaf00004_w_suffix24_eval leaf00004_w_suffix23_join x
#print axioms leaf00004_w_suffix23_join
#print axioms leaf00004_w_suffix23_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
