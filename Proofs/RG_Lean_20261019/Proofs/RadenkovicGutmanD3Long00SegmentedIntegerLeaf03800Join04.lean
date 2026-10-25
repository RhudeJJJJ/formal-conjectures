/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece04
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join05
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix04 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source05.length) leaf03800_w_piece04) leaf03800_w_suffix05)
theorem leaf03800_w_suffix04_join : leaf03800_w_suffix04=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source05.length) leaf03800_w_piece04) leaf03800_w_suffix05 := by decide +kernel
theorem leaf03800_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 12 leaf03800_w_source04)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 12 15
    leaf03800_w_segment04 leaf03800_w_source05 leaf03800_w_source04
    leaf03800_w_piece04 leaf03800_w_suffix05 leaf03800_w_suffix04
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source04)
    leaf03800_w_piece04_identity leaf03800_w_suffix05_eval leaf03800_w_suffix04_join x
#print axioms leaf03800_w_suffix04_join
#print axioms leaf03800_w_suffix04_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
