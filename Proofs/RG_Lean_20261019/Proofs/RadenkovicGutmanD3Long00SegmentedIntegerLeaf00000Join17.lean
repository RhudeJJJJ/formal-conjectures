/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Piece17
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Join18
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix17 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source18.length) leaf00000_w_piece17) leaf00000_w_suffix18)
theorem leaf00000_w_suffix17_join : leaf00000_w_suffix17=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source18.length) leaf00000_w_piece17) leaf00000_w_suffix18 := by decide +kernel
theorem leaf00000_w_suffix17_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix17) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 51 leaf00000_w_source17)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 51 54
    leaf00000_w_segment17 leaf00000_w_source18 leaf00000_w_source17
    leaf00000_w_piece17 leaf00000_w_suffix18 leaf00000_w_suffix17
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source17)
    leaf00000_w_piece17_identity leaf00000_w_suffix18_eval leaf00000_w_suffix17_join x
#print axioms leaf00000_w_suffix17_join
#print axioms leaf00000_w_suffix17_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
