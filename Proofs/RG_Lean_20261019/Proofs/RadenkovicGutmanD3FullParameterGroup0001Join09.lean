/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Piece09
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Join10
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00004_w_suffix09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source10.length) leaf00004_w_piece09) leaf00004_w_suffix10)
theorem leaf00004_w_suffix09_join : leaf00004_w_suffix09=NestedInteger.add (NestedInteger.scale (32000^leaf00004_w_source10.length) leaf00004_w_piece09) leaf00004_w_suffix10 := by decide +kernel
theorem leaf00004_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00004_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 27 leaf00004_w_source09)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 27 30
    leaf00004_w_segment09 leaf00004_w_source10 leaf00004_w_source09
    leaf00004_w_piece09 leaf00004_w_suffix10 leaf00004_w_suffix09
    (by decide +kernel) (List.take_append_drop 3 leaf00004_w_source09)
    leaf00004_w_piece09_identity leaf00004_w_suffix10_eval leaf00004_w_suffix09_join x
#print axioms leaf00004_w_suffix09_join
#print axioms leaf00004_w_suffix09_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
