/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Piece05
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Join06
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_suffix05 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source06.length) leaf00005_w_piece05) leaf00005_w_suffix06)
theorem leaf00005_w_suffix05_join : leaf00005_w_suffix05=NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source06.length) leaf00005_w_piece05) leaf00005_w_suffix06 := by decide +kernel
theorem leaf00005_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00005_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 15 leaf00005_w_source05)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 15 18
    leaf00005_w_segment05 leaf00005_w_source06 leaf00005_w_source05
    leaf00005_w_piece05 leaf00005_w_suffix06 leaf00005_w_suffix05
    (by decide +kernel) (List.take_append_drop 3 leaf00005_w_source05)
    leaf00005_w_piece05_identity leaf00005_w_suffix06_eval leaf00005_w_suffix05_join x
#print axioms leaf00005_w_suffix05_join
#print axioms leaf00005_w_suffix05_eval
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
