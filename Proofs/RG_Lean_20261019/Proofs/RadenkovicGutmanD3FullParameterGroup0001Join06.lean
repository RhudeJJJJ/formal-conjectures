/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Piece06
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Join07
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00004_w_suffix06 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source07.length) leaf00004_w_piece06) leaf00004_w_suffix07)
theorem leaf00004_w_suffix06_join : leaf00004_w_suffix06=NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source07.length) leaf00004_w_piece06) leaf00004_w_suffix07 := by decide +kernel
theorem leaf00004_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00004_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 18 leaf00004_w_source06)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 18 21
    leaf00004_w_segment06 leaf00004_w_source07 leaf00004_w_source06
    leaf00004_w_piece06 leaf00004_w_suffix07 leaf00004_w_suffix06
    (by decide +kernel) (List.take_append_drop 3 leaf00004_w_source06)
    leaf00004_w_piece06_identity leaf00004_w_suffix07_eval leaf00004_w_suffix06_join x
#print axioms leaf00004_w_suffix06_join
#print axioms leaf00004_w_suffix06_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
