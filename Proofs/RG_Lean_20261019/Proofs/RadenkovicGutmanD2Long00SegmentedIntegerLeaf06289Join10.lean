/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece10
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join11
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix10 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source11.length) leaf06289_w_piece10) leaf06289_w_suffix11)
theorem leaf06289_w_suffix10_join : leaf06289_w_suffix10=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source11.length) leaf06289_w_piece10) leaf06289_w_suffix11 := by decide +kernel
theorem leaf06289_w_suffix10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix10) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 30 leaf06289_w_source10)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 30 33
    leaf06289_w_segment10 leaf06289_w_source11 leaf06289_w_source10
    leaf06289_w_piece10 leaf06289_w_suffix11 leaf06289_w_suffix10
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source10)
    leaf06289_w_piece10_identity leaf06289_w_suffix11_eval leaf06289_w_suffix10_join x
#print axioms leaf06289_w_suffix10_join
#print axioms leaf06289_w_suffix10_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
