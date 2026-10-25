/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Piece04
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Join05
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_suffix04 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source05.length) leaf00005_w_piece04) leaf00005_w_suffix05)
theorem leaf00005_w_suffix04_join : leaf00005_w_suffix04=NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source05.length) leaf00005_w_piece04) leaf00005_w_suffix05 := by decide +kernel
theorem leaf00005_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00005_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 12 leaf00005_w_source04)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 12 15
    leaf00005_w_segment04 leaf00005_w_source05 leaf00005_w_source04
    leaf00005_w_piece04 leaf00005_w_suffix05 leaf00005_w_suffix04
    (by decide +kernel) (List.take_append_drop 3 leaf00005_w_source04)
    leaf00005_w_piece04_identity leaf00005_w_suffix05_eval leaf00005_w_suffix04_join x
#print axioms leaf00005_w_suffix04_join
#print axioms leaf00005_w_suffix04_eval
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
