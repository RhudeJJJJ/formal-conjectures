/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Piece03
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Join04
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_suffix03 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source04.length) leaf00005_w_piece03) leaf00005_w_suffix04)
theorem leaf00005_w_suffix03_join : leaf00005_w_suffix03=NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source04.length) leaf00005_w_piece03) leaf00005_w_suffix04 := by decide +kernel
theorem leaf00005_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00005_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 9 leaf00005_w_source03)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 9 12
    leaf00005_w_segment03 leaf00005_w_source04 leaf00005_w_source03
    leaf00005_w_piece03 leaf00005_w_suffix04 leaf00005_w_suffix03
    (by decide +kernel) (List.take_append_drop 3 leaf00005_w_source03)
    leaf00005_w_piece03_identity leaf00005_w_suffix04_eval leaf00005_w_suffix03_join x
#print axioms leaf00005_w_suffix03_join
#print axioms leaf00005_w_suffix03_eval
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
