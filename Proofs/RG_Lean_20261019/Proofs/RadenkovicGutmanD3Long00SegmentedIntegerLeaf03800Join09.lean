/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece09
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join10
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source10.length) leaf03800_w_piece09) leaf03800_w_suffix10)
theorem leaf03800_w_suffix09_join : leaf03800_w_suffix09=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source10.length) leaf03800_w_piece09) leaf03800_w_suffix10 := by decide +kernel
theorem leaf03800_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 27 leaf03800_w_source09)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 27 30
    leaf03800_w_segment09 leaf03800_w_source10 leaf03800_w_source09
    leaf03800_w_piece09 leaf03800_w_suffix10 leaf03800_w_suffix09
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source09)
    leaf03800_w_piece09_identity leaf03800_w_suffix10_eval leaf03800_w_suffix09_join x
#print axioms leaf03800_w_suffix09_join
#print axioms leaf03800_w_suffix09_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
