/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece26
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join27
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source27.length) leaf03800_w_piece26) leaf03800_w_suffix27)
theorem leaf03800_w_suffix26_join : leaf03800_w_suffix26=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source27.length) leaf03800_w_piece26) leaf03800_w_suffix27 := by decide +kernel
theorem leaf03800_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 78 leaf03800_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 78 81
    leaf03800_w_segment26 leaf03800_w_source27 leaf03800_w_source26
    leaf03800_w_piece26 leaf03800_w_suffix27 leaf03800_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source26)
    leaf03800_w_piece26_identity leaf03800_w_suffix27_eval leaf03800_w_suffix26_join x
#print axioms leaf03800_w_suffix26_join
#print axioms leaf03800_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
