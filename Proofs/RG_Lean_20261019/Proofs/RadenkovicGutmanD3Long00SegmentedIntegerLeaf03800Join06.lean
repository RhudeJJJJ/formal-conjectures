/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Piece06
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf03800Join07
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_suffix06 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source07.length) leaf03800_w_piece06) leaf03800_w_suffix07)
theorem leaf03800_w_suffix06_join : leaf03800_w_suffix06=NestedInteger.add (NestedInteger.scale (4096^leaf03800_w_source07.length) leaf03800_w_piece06) leaf03800_w_suffix07 := by decide +kernel
theorem leaf03800_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf03800_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 18 leaf03800_w_source06)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 18 21
    leaf03800_w_segment06 leaf03800_w_source07 leaf03800_w_source06
    leaf03800_w_piece06 leaf03800_w_suffix07 leaf03800_w_suffix06
    (by decide +kernel) (List.take_append_drop 3 leaf03800_w_source06)
    leaf03800_w_piece06_identity leaf03800_w_suffix07_eval leaf03800_w_suffix06_join x
#print axioms leaf03800_w_suffix06_join
#print axioms leaf03800_w_suffix06_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf03800
