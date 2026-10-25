/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece13
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join14
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source14.length) leaf01900_w_piece13) leaf01900_w_suffix14)
theorem leaf01900_w_suffix13_join : leaf01900_w_suffix13=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source14.length) leaf01900_w_piece13) leaf01900_w_suffix14 := by decide +kernel
theorem leaf01900_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 39 leaf01900_w_source13)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 39 42
    leaf01900_w_segment13 leaf01900_w_source14 leaf01900_w_source13
    leaf01900_w_piece13 leaf01900_w_suffix14 leaf01900_w_suffix13
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source13)
    leaf01900_w_piece13_identity leaf01900_w_suffix14_eval leaf01900_w_suffix13_join x
#print axioms leaf01900_w_suffix13_join
#print axioms leaf01900_w_suffix13_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
