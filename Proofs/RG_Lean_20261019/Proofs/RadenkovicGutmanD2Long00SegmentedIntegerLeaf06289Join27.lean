/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece27
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join28
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source28.length) leaf06289_w_piece27) leaf06289_w_suffix28)
theorem leaf06289_w_suffix27_join : leaf06289_w_suffix27=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source28.length) leaf06289_w_piece27) leaf06289_w_suffix28 := by decide +kernel
theorem leaf06289_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 81 leaf06289_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 81 84
    leaf06289_w_segment27 leaf06289_w_source28 leaf06289_w_source27
    leaf06289_w_piece27 leaf06289_w_suffix28 leaf06289_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source27)
    leaf06289_w_piece27_identity leaf06289_w_suffix28_eval leaf06289_w_suffix27_join x
#print axioms leaf06289_w_suffix27_join
#print axioms leaf06289_w_suffix27_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
