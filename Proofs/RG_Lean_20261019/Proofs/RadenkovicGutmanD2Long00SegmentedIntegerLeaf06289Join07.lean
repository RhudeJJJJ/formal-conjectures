/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece07
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join08
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix07 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source08.length) leaf06289_w_piece07) leaf06289_w_suffix08)
theorem leaf06289_w_suffix07_join : leaf06289_w_suffix07=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source08.length) leaf06289_w_piece07) leaf06289_w_suffix08 := by decide +kernel
theorem leaf06289_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 21 leaf06289_w_source07)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 21 24
    leaf06289_w_segment07 leaf06289_w_source08 leaf06289_w_source07
    leaf06289_w_piece07 leaf06289_w_suffix08 leaf06289_w_suffix07
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source07)
    leaf06289_w_piece07_identity leaf06289_w_suffix08_eval leaf06289_w_suffix07_join x
#print axioms leaf06289_w_suffix07_join
#print axioms leaf06289_w_suffix07_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
