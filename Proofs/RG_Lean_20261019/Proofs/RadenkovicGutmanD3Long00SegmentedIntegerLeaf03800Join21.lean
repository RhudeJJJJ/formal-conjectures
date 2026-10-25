/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece21
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join22
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix21 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source22.length) leaf03800_w_piece21) leaf03800_w_suffix22)
theorem leaf03800_w_suffix21_join : leaf03800_w_suffix21=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source22.length) leaf03800_w_piece21) leaf03800_w_suffix22 := by decide +kernel
theorem leaf03800_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 63 leaf03800_w_source21)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 63 66
    leaf03800_w_segment21 leaf03800_w_source22 leaf03800_w_source21
    leaf03800_w_piece21 leaf03800_w_suffix22 leaf03800_w_suffix21
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source21)
    leaf03800_w_piece21_identity leaf03800_w_suffix22_eval leaf03800_w_suffix21_join x
#print axioms leaf03800_w_suffix21_join
#print axioms leaf03800_w_suffix21_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
