/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece06
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Join07
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix06 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source07.length) leaf01900_w_piece06) leaf01900_w_suffix07)
theorem leaf01900_w_suffix06_join : leaf01900_w_suffix06=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source07.length) leaf01900_w_piece06) leaf01900_w_suffix07 := by decide +kernel
theorem leaf01900_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 18 leaf01900_w_source06)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 18 21
    leaf01900_w_segment06 leaf01900_w_source07 leaf01900_w_source06
    leaf01900_w_piece06 leaf01900_w_suffix07 leaf01900_w_suffix06
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source06)
    leaf01900_w_piece06_identity leaf01900_w_suffix07_eval leaf01900_w_suffix06_join x
#print axioms leaf01900_w_suffix06_join
#print axioms leaf01900_w_suffix06_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
