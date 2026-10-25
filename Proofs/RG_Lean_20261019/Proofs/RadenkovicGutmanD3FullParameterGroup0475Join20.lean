/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece20
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join21
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source21.length) leaf01900_w_piece20) leaf01900_w_suffix21)
theorem leaf01900_w_suffix20_join : leaf01900_w_suffix20=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source21.length) leaf01900_w_piece20) leaf01900_w_suffix21 := by decide +kernel
theorem leaf01900_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 60 leaf01900_w_source20)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 60 63
    leaf01900_w_segment20 leaf01900_w_source21 leaf01900_w_source20
    leaf01900_w_piece20 leaf01900_w_suffix21 leaf01900_w_suffix20
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source20)
    leaf01900_w_piece20_identity leaf01900_w_suffix21_eval leaf01900_w_suffix20_join x
#print axioms leaf01900_w_suffix20_join
#print axioms leaf01900_w_suffix20_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
