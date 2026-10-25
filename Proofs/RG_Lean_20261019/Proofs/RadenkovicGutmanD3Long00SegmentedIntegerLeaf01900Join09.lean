/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece09
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Join10
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source10.length) leaf01900_w_piece09) leaf01900_w_suffix10)
theorem leaf01900_w_suffix09_join : leaf01900_w_suffix09=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source10.length) leaf01900_w_piece09) leaf01900_w_suffix10 := by decide +kernel
theorem leaf01900_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 27 leaf01900_w_source09)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 27 30
    leaf01900_w_segment09 leaf01900_w_source10 leaf01900_w_source09
    leaf01900_w_piece09 leaf01900_w_suffix10 leaf01900_w_suffix09
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source09)
    leaf01900_w_piece09_identity leaf01900_w_suffix10_eval leaf01900_w_suffix09_join x
#print axioms leaf01900_w_suffix09_join
#print axioms leaf01900_w_suffix09_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
