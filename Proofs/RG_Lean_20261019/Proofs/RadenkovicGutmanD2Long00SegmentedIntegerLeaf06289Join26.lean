/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece26
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join27
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source27.length) leaf06289_w_piece26) leaf06289_w_suffix27)
theorem leaf06289_w_suffix26_join : leaf06289_w_suffix26=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source27.length) leaf06289_w_piece26) leaf06289_w_suffix27 := by decide +kernel
theorem leaf06289_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 78 leaf06289_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 78 81
    leaf06289_w_segment26 leaf06289_w_source27 leaf06289_w_source26
    leaf06289_w_piece26 leaf06289_w_suffix27 leaf06289_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source26)
    leaf06289_w_piece26_identity leaf06289_w_suffix27_eval leaf06289_w_suffix26_join x
#print axioms leaf06289_w_suffix26_join
#print axioms leaf06289_w_suffix26_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
