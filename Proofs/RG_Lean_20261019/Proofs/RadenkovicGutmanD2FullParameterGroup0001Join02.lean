/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Piece02
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Join03
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_suffix02 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source03.length) leaf00005_w_piece02) leaf00005_w_suffix03)
theorem leaf00005_w_suffix02_join : leaf00005_w_suffix02=NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source03.length) leaf00005_w_piece02) leaf00005_w_suffix03 := by decide +kernel
theorem leaf00005_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00005_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 6 leaf00005_w_source02)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 6 9
    leaf00005_w_segment02 leaf00005_w_source03 leaf00005_w_source02
    leaf00005_w_piece02 leaf00005_w_suffix03 leaf00005_w_suffix02
    (by decide +kernel) (List.take_append_drop 3 leaf00005_w_source02)
    leaf00005_w_piece02_identity leaf00005_w_suffix03_eval leaf00005_w_suffix02_join x
#print axioms leaf00005_w_suffix02_join
#print axioms leaf00005_w_suffix02_eval
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
