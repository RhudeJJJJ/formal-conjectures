/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece23
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join24
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix23 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source24.length) leaf01900_w_piece23) leaf01900_w_suffix24)
theorem leaf01900_w_suffix23_join : leaf01900_w_suffix23=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source24.length) leaf01900_w_piece23) leaf01900_w_suffix24 := by decide +kernel
theorem leaf01900_w_suffix23_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix23) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 69 leaf01900_w_source23)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 69 72
    leaf01900_w_segment23 leaf01900_w_source24 leaf01900_w_source23
    leaf01900_w_piece23 leaf01900_w_suffix24 leaf01900_w_suffix23
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source23)
    leaf01900_w_piece23_identity leaf01900_w_suffix24_eval leaf01900_w_suffix23_join x
#print axioms leaf01900_w_suffix23_join
#print axioms leaf01900_w_suffix23_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
