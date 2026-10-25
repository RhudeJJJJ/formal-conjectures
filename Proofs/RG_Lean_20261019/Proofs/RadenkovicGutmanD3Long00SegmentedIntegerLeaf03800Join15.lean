/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece15
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join16
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix15 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source16.length) leaf03800_w_piece15) leaf03800_w_suffix16)
theorem leaf03800_w_suffix15_join : leaf03800_w_suffix15=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source16.length) leaf03800_w_piece15) leaf03800_w_suffix16 := by decide +kernel
theorem leaf03800_w_suffix15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix15) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 45 leaf03800_w_source15)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 45 48
    leaf03800_w_segment15 leaf03800_w_source16 leaf03800_w_source15
    leaf03800_w_piece15 leaf03800_w_suffix16 leaf03800_w_suffix15
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source15)
    leaf03800_w_piece15_identity leaf03800_w_suffix16_eval leaf03800_w_suffix15_join x
#print axioms leaf03800_w_suffix15_join
#print axioms leaf03800_w_suffix15_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
