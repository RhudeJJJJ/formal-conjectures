/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Piece18
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Join19
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_suffix18 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source19.length) leaf00005_w_piece18) leaf00005_w_suffix19)
theorem leaf00005_w_suffix18_join : leaf00005_w_suffix18=NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source19.length) leaf00005_w_piece18) leaf00005_w_suffix19 := by decide +kernel
theorem leaf00005_w_suffix18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00005_w_suffix18) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 54 leaf00005_w_source18)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 54 57
    leaf00005_w_segment18 leaf00005_w_source19 leaf00005_w_source18
    leaf00005_w_piece18 leaf00005_w_suffix19 leaf00005_w_suffix18
    (by decide +kernel) (List.take_append_drop 3 leaf00005_w_source18)
    leaf00005_w_piece18_identity leaf00005_w_suffix19_eval leaf00005_w_suffix18_join x
#print axioms leaf00005_w_suffix18_join
#print axioms leaf00005_w_suffix18_eval
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
