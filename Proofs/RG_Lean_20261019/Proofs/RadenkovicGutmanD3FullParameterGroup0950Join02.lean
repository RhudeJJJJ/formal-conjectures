/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Piece02
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Join03
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix02 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source03.length) leaf03800_w_piece02) leaf03800_w_suffix03)
theorem leaf03800_w_suffix02_join : leaf03800_w_suffix02=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source03.length) leaf03800_w_piece02) leaf03800_w_suffix03 := by decide +kernel
theorem leaf03800_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 6 leaf03800_w_source02)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 6 9
    leaf03800_w_segment02 leaf03800_w_source03 leaf03800_w_source02
    leaf03800_w_piece02 leaf03800_w_suffix03 leaf03800_w_suffix02
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source02)
    leaf03800_w_piece02_identity leaf03800_w_suffix03_eval leaf03800_w_suffix02_join x
#print axioms leaf03800_w_suffix02_join
#print axioms leaf03800_w_suffix02_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
