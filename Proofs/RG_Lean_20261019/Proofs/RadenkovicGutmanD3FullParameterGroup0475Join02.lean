/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Piece02
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Join03
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix02 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source03.length) leaf01900_w_piece02) leaf01900_w_suffix03)
theorem leaf01900_w_suffix02_join : leaf01900_w_suffix02=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source03.length) leaf01900_w_piece02) leaf01900_w_suffix03 := by decide +kernel
theorem leaf01900_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 6 leaf01900_w_source02)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 6 9
    leaf01900_w_segment02 leaf01900_w_source03 leaf01900_w_source02
    leaf01900_w_piece02 leaf01900_w_suffix03 leaf01900_w_suffix02
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source02)
    leaf01900_w_piece02_identity leaf01900_w_suffix03_eval leaf01900_w_suffix02_join x
#print axioms leaf01900_w_suffix02_join
#print axioms leaf01900_w_suffix02_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
