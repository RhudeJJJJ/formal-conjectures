/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Piece03
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf00000Join04
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_suffix03 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source04.length) leaf00000_w_piece03) leaf00000_w_suffix04)
theorem leaf00000_w_suffix03_join : leaf00000_w_suffix03=NestedInteger.add (NestedInteger.scale (32000^leaf00000_w_source04.length) leaf00000_w_piece03) leaf00000_w_suffix04 := by decide +kernel
theorem leaf00000_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00000_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 32 1 32000 9 leaf00000_w_source03)) x :=
  IntegerOuterJoinedEvaluation.joined 32 1 32000 9 12
    leaf00000_w_segment03 leaf00000_w_source04 leaf00000_w_source03
    leaf00000_w_piece03 leaf00000_w_suffix04 leaf00000_w_suffix03
    (by decide +kernel) (List.take_append_drop 3 leaf00000_w_source03)
    leaf00000_w_piece03_identity leaf00000_w_suffix04_eval leaf00000_w_suffix03_join x
#print axioms leaf00000_w_suffix03_join
#print axioms leaf00000_w_suffix03_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
