/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece14
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join15
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix14 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source15.length) leaf06289_w_piece14) leaf06289_w_suffix15)
theorem leaf06289_w_suffix14_join : leaf06289_w_suffix14=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source15.length) leaf06289_w_piece14) leaf06289_w_suffix15 := by decide +kernel
theorem leaf06289_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 42 leaf06289_w_source14)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 42 45
    leaf06289_w_segment14 leaf06289_w_source15 leaf06289_w_source14
    leaf06289_w_piece14 leaf06289_w_suffix15 leaf06289_w_suffix14
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source14)
    leaf06289_w_piece14_identity leaf06289_w_suffix15_eval leaf06289_w_suffix14_join x
#print axioms leaf06289_w_suffix14_join
#print axioms leaf06289_w_suffix14_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
