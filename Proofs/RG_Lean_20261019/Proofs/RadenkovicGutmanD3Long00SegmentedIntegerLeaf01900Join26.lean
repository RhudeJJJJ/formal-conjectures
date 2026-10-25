/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece26
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Join27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source27.length) leaf01900_w_piece26) leaf01900_w_suffix27)
theorem leaf01900_w_suffix26_join : leaf01900_w_suffix26=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source27.length) leaf01900_w_piece26) leaf01900_w_suffix27 := by decide +kernel
theorem leaf01900_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 78 leaf01900_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 78 81
    leaf01900_w_segment26 leaf01900_w_source27 leaf01900_w_source26
    leaf01900_w_piece26 leaf01900_w_suffix27 leaf01900_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source26)
    leaf01900_w_piece26_identity leaf01900_w_suffix27_eval leaf01900_w_suffix26_join x
#print axioms leaf01900_w_suffix26_join
#print axioms leaf01900_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
