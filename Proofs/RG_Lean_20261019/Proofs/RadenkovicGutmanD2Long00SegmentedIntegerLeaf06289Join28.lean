/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece28
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix28 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source29.length) leaf06289_w_piece28) leaf06289_w_suffix29)
theorem leaf06289_w_suffix28_join : leaf06289_w_suffix28=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source29.length) leaf06289_w_piece28) leaf06289_w_suffix29 := by decide +kernel
theorem leaf06289_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 84 leaf06289_w_source28)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 84 87
    leaf06289_w_segment28 leaf06289_w_source29 leaf06289_w_source28
    leaf06289_w_piece28 leaf06289_w_suffix29 leaf06289_w_suffix28
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source28)
    leaf06289_w_piece28_identity leaf06289_w_suffix29_eval leaf06289_w_suffix28_join x
#print axioms leaf06289_w_suffix28_join
#print axioms leaf06289_w_suffix28_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
