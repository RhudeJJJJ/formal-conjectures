/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Piece19
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Join20
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_suffix19 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source20.length) leaf00005_w_piece19) leaf00005_w_suffix20)
theorem leaf00005_w_suffix19_join : leaf00005_w_suffix19=NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source20.length) leaf00005_w_piece19) leaf00005_w_suffix20 := by decide +kernel
theorem leaf00005_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00005_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 57 leaf00005_w_source19)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 57 60
    leaf00005_w_segment19 leaf00005_w_source20 leaf00005_w_source19
    leaf00005_w_piece19 leaf00005_w_suffix20 leaf00005_w_suffix19
    (by decide +kernel) (List.take_append_drop 3 leaf00005_w_source19)
    leaf00005_w_piece19_identity leaf00005_w_suffix20_eval leaf00005_w_suffix19_join x
#print axioms leaf00005_w_suffix19_join
#print axioms leaf00005_w_suffix19_eval
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
