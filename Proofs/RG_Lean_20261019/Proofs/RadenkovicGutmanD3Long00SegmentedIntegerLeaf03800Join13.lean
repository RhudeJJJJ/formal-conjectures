/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece13
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join14
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source14.length) leaf03800_w_piece13) leaf03800_w_suffix14)
theorem leaf03800_w_suffix13_join : leaf03800_w_suffix13=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source14.length) leaf03800_w_piece13) leaf03800_w_suffix14 := by decide +kernel
theorem leaf03800_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 39 leaf03800_w_source13)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 39 42
    leaf03800_w_segment13 leaf03800_w_source14 leaf03800_w_source13
    leaf03800_w_piece13 leaf03800_w_suffix14 leaf03800_w_suffix13
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source13)
    leaf03800_w_piece13_identity leaf03800_w_suffix14_eval leaf03800_w_suffix13_join x
#print axioms leaf03800_w_suffix13_join
#print axioms leaf03800_w_suffix13_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
