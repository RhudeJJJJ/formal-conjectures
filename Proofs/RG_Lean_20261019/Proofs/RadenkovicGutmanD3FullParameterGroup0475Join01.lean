/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece01
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source02.length) leaf01900_w_piece01) leaf01900_w_suffix02)
theorem leaf01900_w_suffix01_join : leaf01900_w_suffix01=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source02.length) leaf01900_w_piece01) leaf01900_w_suffix02 := by decide +kernel
theorem leaf01900_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 3 leaf01900_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 3 6
    leaf01900_w_segment01 leaf01900_w_source02 leaf01900_w_source01
    leaf01900_w_piece01 leaf01900_w_suffix02 leaf01900_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source01)
    leaf01900_w_piece01_identity leaf01900_w_suffix02_eval leaf01900_w_suffix01_join x
#print axioms leaf01900_w_suffix01_join
#print axioms leaf01900_w_suffix01_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
