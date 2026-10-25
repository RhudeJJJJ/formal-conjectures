/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece20
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join21
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source21.length) leaf03800_w_piece20) leaf03800_w_suffix21)
theorem leaf03800_w_suffix20_join : leaf03800_w_suffix20=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source21.length) leaf03800_w_piece20) leaf03800_w_suffix21 := by decide +kernel
theorem leaf03800_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 60 leaf03800_w_source20)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 60 63
    leaf03800_w_segment20 leaf03800_w_source21 leaf03800_w_source20
    leaf03800_w_piece20 leaf03800_w_suffix21 leaf03800_w_suffix20
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source20)
    leaf03800_w_piece20_identity leaf03800_w_suffix21_eval leaf03800_w_suffix20_join x
#print axioms leaf03800_w_suffix20_join
#print axioms leaf03800_w_suffix20_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
