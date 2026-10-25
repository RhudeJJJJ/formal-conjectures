/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece18
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Join19
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix18 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source19.length) leaf01900_w_piece18) leaf01900_w_suffix19)
theorem leaf01900_w_suffix18_join : leaf01900_w_suffix18=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source19.length) leaf01900_w_piece18) leaf01900_w_suffix19 := by decide +kernel
theorem leaf01900_w_suffix18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix18) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 54 leaf01900_w_source18)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 54 57
    leaf01900_w_segment18 leaf01900_w_source19 leaf01900_w_source18
    leaf01900_w_piece18 leaf01900_w_suffix19 leaf01900_w_suffix18
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source18)
    leaf01900_w_piece18_identity leaf01900_w_suffix19_eval leaf01900_w_suffix18_join x
#print axioms leaf01900_w_suffix18_join
#print axioms leaf01900_w_suffix18_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
