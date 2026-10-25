/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Piece13
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Join14
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source14.length) leaf00000_w_piece13) leaf00000_w_suffix14)
theorem leaf00000_w_suffix13_join : leaf00000_w_suffix13=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source14.length) leaf00000_w_piece13) leaf00000_w_suffix14 := by decide +kernel
theorem leaf00000_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 39 leaf00000_w_source13)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 39 42
    leaf00000_w_segment13 leaf00000_w_source14 leaf00000_w_source13
    leaf00000_w_piece13 leaf00000_w_suffix14 leaf00000_w_suffix13
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source13)
    leaf00000_w_piece13_identity leaf00000_w_suffix14_eval leaf00000_w_suffix13_join x
#print axioms leaf00000_w_suffix13_join
#print axioms leaf00000_w_suffix13_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
