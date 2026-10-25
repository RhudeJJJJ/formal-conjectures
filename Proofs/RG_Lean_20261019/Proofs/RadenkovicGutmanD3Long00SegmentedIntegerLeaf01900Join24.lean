/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece24
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Join25
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix24 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source25.length) leaf01900_w_piece24) leaf01900_w_suffix25)
theorem leaf01900_w_suffix24_join : leaf01900_w_suffix24=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source25.length) leaf01900_w_piece24) leaf01900_w_suffix25 := by decide +kernel
theorem leaf01900_w_suffix24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix24) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 72 leaf01900_w_source24)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 72 75
    leaf01900_w_segment24 leaf01900_w_source25 leaf01900_w_source24
    leaf01900_w_piece24 leaf01900_w_suffix25 leaf01900_w_suffix24
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source24)
    leaf01900_w_piece24_identity leaf01900_w_suffix25_eval leaf01900_w_suffix24_join x
#print axioms leaf01900_w_suffix24_join
#print axioms leaf01900_w_suffix24_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
