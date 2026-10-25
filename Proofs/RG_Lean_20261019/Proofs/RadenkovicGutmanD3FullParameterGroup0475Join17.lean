/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece17
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join18
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix17 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source18.length) leaf01900_w_piece17) leaf01900_w_suffix18)
theorem leaf01900_w_suffix17_join : leaf01900_w_suffix17=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source18.length) leaf01900_w_piece17) leaf01900_w_suffix18 := by decide +kernel
theorem leaf01900_w_suffix17_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix17) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 51 leaf01900_w_source17)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 51 54
    leaf01900_w_segment17 leaf01900_w_source18 leaf01900_w_source17
    leaf01900_w_piece17 leaf01900_w_suffix18 leaf01900_w_suffix17
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source17)
    leaf01900_w_piece17_identity leaf01900_w_suffix18_eval leaf01900_w_suffix17_join x
#print axioms leaf01900_w_suffix17_join
#print axioms leaf01900_w_suffix17_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
