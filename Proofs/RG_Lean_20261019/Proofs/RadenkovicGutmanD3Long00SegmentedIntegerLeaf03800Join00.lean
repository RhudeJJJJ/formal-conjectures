/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece00
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join01
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source01.length) leaf03800_w_piece00) leaf03800_w_suffix01)
theorem leaf03800_w_affine_join : leaf03800_w_affine=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source01.length) leaf03800_w_piece00) leaf03800_w_suffix01 := by decide +kernel
theorem leaf03800_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 0 leaf03800_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 0 3
    leaf03800_w_segment00 leaf03800_w_source01 leaf03800_w_source00
    leaf03800_w_piece00 leaf03800_w_suffix01 leaf03800_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source00)
    leaf03800_w_piece00_identity leaf03800_w_suffix01_eval leaf03800_w_affine_join x
#print axioms leaf03800_w_affine_join
#print axioms leaf03800_w_affine_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
