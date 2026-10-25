/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece04
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join05
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix04 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source05.length) leaf01900_w_piece04) leaf01900_w_suffix05)
theorem leaf01900_w_suffix04_join : leaf01900_w_suffix04=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source05.length) leaf01900_w_piece04) leaf01900_w_suffix05 := by decide +kernel
theorem leaf01900_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 12 leaf01900_w_source04)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 12 15
    leaf01900_w_segment04 leaf01900_w_source05 leaf01900_w_source04
    leaf01900_w_piece04 leaf01900_w_suffix05 leaf01900_w_suffix04
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source04)
    leaf01900_w_piece04_identity leaf01900_w_suffix05_eval leaf01900_w_suffix04_join x
#print axioms leaf01900_w_suffix04_join
#print axioms leaf01900_w_suffix04_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
