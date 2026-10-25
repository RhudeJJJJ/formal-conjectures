/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece23
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join24
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix23 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source24.length) leaf03800_w_piece23) leaf03800_w_suffix24)
theorem leaf03800_w_suffix23_join : leaf03800_w_suffix23=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source24.length) leaf03800_w_piece23) leaf03800_w_suffix24 := by decide +kernel
theorem leaf03800_w_suffix23_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix23) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 69 leaf03800_w_source23)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 69 72
    leaf03800_w_segment23 leaf03800_w_source24 leaf03800_w_source23
    leaf03800_w_piece23 leaf03800_w_suffix24 leaf03800_w_suffix23
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source23)
    leaf03800_w_piece23_identity leaf03800_w_suffix24_eval leaf03800_w_suffix23_join x
#print axioms leaf03800_w_suffix23_join
#print axioms leaf03800_w_suffix23_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
