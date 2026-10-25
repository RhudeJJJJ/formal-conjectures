/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Piece15
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Join16
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix15 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source16.length) leaf00000_w_piece15) leaf00000_w_suffix16)
theorem leaf00000_w_suffix15_join : leaf00000_w_suffix15=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source16.length) leaf00000_w_piece15) leaf00000_w_suffix16 := by decide +kernel
theorem leaf00000_w_suffix15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix15) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 45 leaf00000_w_source15)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 45 48
    leaf00000_w_segment15 leaf00000_w_source16 leaf00000_w_source15
    leaf00000_w_piece15 leaf00000_w_suffix16 leaf00000_w_suffix15
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source15)
    leaf00000_w_piece15_identity leaf00000_w_suffix16_eval leaf00000_w_suffix15_join x
#print axioms leaf00000_w_suffix15_join
#print axioms leaf00000_w_suffix15_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
