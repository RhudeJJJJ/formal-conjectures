/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece01
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join02
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source02.length) leaf03800_w_piece01) leaf03800_w_suffix02)
theorem leaf03800_w_suffix01_join : leaf03800_w_suffix01=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source02.length) leaf03800_w_piece01) leaf03800_w_suffix02 := by decide +kernel
theorem leaf03800_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 3 leaf03800_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 3 6
    leaf03800_w_segment01 leaf03800_w_source02 leaf03800_w_source01
    leaf03800_w_piece01 leaf03800_w_suffix02 leaf03800_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source01)
    leaf03800_w_piece01_identity leaf03800_w_suffix02_eval leaf03800_w_suffix01_join x
#print axioms leaf03800_w_suffix01_join
#print axioms leaf03800_w_suffix01_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
