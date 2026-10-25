/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece11
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Join12
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix11 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source12.length) leaf01900_w_piece11) leaf01900_w_suffix12)
theorem leaf01900_w_suffix11_join : leaf01900_w_suffix11=NestedInteger.add (NestedInteger.scale (12800^leaf01900_w_source12.length) leaf01900_w_piece11) leaf01900_w_suffix12 := by decide +kernel
theorem leaf01900_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 33 leaf01900_w_source11)) x :=
  IntegerOuterJoinedEvaluation.joined 559 3 12800 33 36
    leaf01900_w_segment11 leaf01900_w_source12 leaf01900_w_source11
    leaf01900_w_piece11 leaf01900_w_suffix12 leaf01900_w_suffix11
    (by decide +kernel) (List.take_append_drop 3 leaf01900_w_source11)
    leaf01900_w_piece11_identity leaf01900_w_suffix12_eval leaf01900_w_suffix11_join x
#print axioms leaf01900_w_suffix11_join
#print axioms leaf01900_w_suffix11_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
