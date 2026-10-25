/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece18
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join19
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix18 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source19.length) leaf06289_w_piece18) leaf06289_w_suffix19)
theorem leaf06289_w_suffix18_join : leaf06289_w_suffix18=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source19.length) leaf06289_w_piece18) leaf06289_w_suffix19 := by decide +kernel
theorem leaf06289_w_suffix18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix18) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 54 leaf06289_w_source18)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 54 57
    leaf06289_w_segment18 leaf06289_w_source19 leaf06289_w_source18
    leaf06289_w_piece18 leaf06289_w_suffix19 leaf06289_w_suffix18
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source18)
    leaf06289_w_piece18_identity leaf06289_w_suffix19_eval leaf06289_w_suffix18_join x
#print axioms leaf06289_w_suffix18_join
#print axioms leaf06289_w_suffix18_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
