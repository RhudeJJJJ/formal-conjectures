/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece16
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Join17
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix16 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source17.length) leaf01900_w_piece16) leaf01900_w_suffix17)
theorem leaf01900_w_suffix16_join : leaf01900_w_suffix16=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source17.length) leaf01900_w_piece16) leaf01900_w_suffix17 := by decide +kernel
theorem leaf01900_w_suffix16_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix16) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 48 leaf01900_w_source16)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 48 51
    leaf01900_w_segment16 leaf01900_w_source17 leaf01900_w_source16
    leaf01900_w_piece16 leaf01900_w_suffix17 leaf01900_w_suffix16
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source16)
    leaf01900_w_piece16_identity leaf01900_w_suffix17_eval leaf01900_w_suffix16_join x
#print axioms leaf01900_w_suffix16_join
#print axioms leaf01900_w_suffix16_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
