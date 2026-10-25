/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece05
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join06
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix05 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source06.length) leaf01900_w_piece05) leaf01900_w_suffix06)
theorem leaf01900_w_suffix05_join : leaf01900_w_suffix05=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source06.length) leaf01900_w_piece05) leaf01900_w_suffix06 := by decide +kernel
theorem leaf01900_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 15 leaf01900_w_source05)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 15 18
    leaf01900_w_segment05 leaf01900_w_source06 leaf01900_w_source05
    leaf01900_w_piece05 leaf01900_w_suffix06 leaf01900_w_suffix05
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source05)
    leaf01900_w_piece05_identity leaf01900_w_suffix06_eval leaf01900_w_suffix05_join x
#print axioms leaf01900_w_suffix05_join
#print axioms leaf01900_w_suffix05_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
