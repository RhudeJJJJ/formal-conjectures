/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Piece14
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Join15
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00004_w_suffix14 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source15.length) leaf00004_w_piece14) leaf00004_w_suffix15)
theorem leaf00004_w_suffix14_join : leaf00004_w_suffix14=NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source15.length) leaf00004_w_piece14) leaf00004_w_suffix15 := by decide +kernel
theorem leaf00004_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00004_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 42 leaf00004_w_source14)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 42 45
    leaf00004_w_segment14 leaf00004_w_source15 leaf00004_w_source14
    leaf00004_w_piece14 leaf00004_w_suffix15 leaf00004_w_suffix14
    (by decide +kernel) (List.take_append_drop 3 leaf00004_w_source14)
    leaf00004_w_piece14_identity leaf00004_w_suffix15_eval leaf00004_w_suffix14_join x
#print axioms leaf00004_w_suffix14_join
#print axioms leaf00004_w_suffix14_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
