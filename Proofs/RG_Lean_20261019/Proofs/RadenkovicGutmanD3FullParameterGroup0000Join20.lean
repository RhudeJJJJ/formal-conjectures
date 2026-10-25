/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Piece20
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Join21
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source21.length) leaf00000_w_piece20) leaf00000_w_suffix21)
theorem leaf00000_w_suffix20_join : leaf00000_w_suffix20=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source21.length) leaf00000_w_piece20) leaf00000_w_suffix21 := by decide +kernel
theorem leaf00000_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 60 leaf00000_w_source20)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 60 63
    leaf00000_w_segment20 leaf00000_w_source21 leaf00000_w_source20
    leaf00000_w_piece20 leaf00000_w_suffix21 leaf00000_w_suffix20
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source20)
    leaf00000_w_piece20_identity leaf00000_w_suffix21_eval leaf00000_w_suffix20_join x
#print axioms leaf00000_w_suffix20_join
#print axioms leaf00000_w_suffix20_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
