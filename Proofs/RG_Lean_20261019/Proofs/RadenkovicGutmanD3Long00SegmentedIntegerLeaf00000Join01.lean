/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Piece01
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Join02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source02.length) leaf00000_w_piece01) leaf00000_w_suffix02)
theorem leaf00000_w_suffix01_join : leaf00000_w_suffix01=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source02.length) leaf00000_w_piece01) leaf00000_w_suffix02 := by decide +kernel
theorem leaf00000_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 3 leaf00000_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 3 6
    leaf00000_w_segment01 leaf00000_w_source02 leaf00000_w_source01
    leaf00000_w_piece01 leaf00000_w_suffix02 leaf00000_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source01)
    leaf00000_w_piece01_identity leaf00000_w_suffix02_eval leaf00000_w_suffix01_join x
#print axioms leaf00000_w_suffix01_join
#print axioms leaf00000_w_suffix01_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
