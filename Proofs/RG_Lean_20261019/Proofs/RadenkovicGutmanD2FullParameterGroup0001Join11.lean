/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Piece11
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Join12
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_suffix11 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source12.length) leaf00005_w_piece11) leaf00005_w_suffix12)
theorem leaf00005_w_suffix11_join : leaf00005_w_suffix11=NestedInteger.add (NestedInteger.scale (32000^leaf00005_w_source12.length) leaf00005_w_piece11) leaf00005_w_suffix12 := by decide +kernel
theorem leaf00005_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00005_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 33 leaf00005_w_source11)) x :=
  IntegerOuterJoinedEvaluation.joined 33 1 32000 33 36
    leaf00005_w_segment11 leaf00005_w_source12 leaf00005_w_source11
    leaf00005_w_piece11 leaf00005_w_suffix12 leaf00005_w_suffix11
    (by decide +kernel) (List.take_append_drop 3 leaf00005_w_source11)
    leaf00005_w_piece11_identity leaf00005_w_suffix12_eval leaf00005_w_suffix11_join x
#print axioms leaf00005_w_suffix11_join
#print axioms leaf00005_w_suffix11_eval
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
