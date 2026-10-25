/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece04
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join05
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix04 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source05.length) leaf06289_w_piece04) leaf06289_w_suffix05)
theorem leaf06289_w_suffix04_join : leaf06289_w_suffix04=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source05.length) leaf06289_w_piece04) leaf06289_w_suffix05 := by decide +kernel
theorem leaf06289_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 12 leaf06289_w_source04)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 12 15
    leaf06289_w_segment04 leaf06289_w_source05 leaf06289_w_source04
    leaf06289_w_piece04 leaf06289_w_suffix05 leaf06289_w_suffix04
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source04)
    leaf06289_w_piece04_identity leaf06289_w_suffix05_eval leaf06289_w_suffix04_join x
#print axioms leaf06289_w_suffix04_join
#print axioms leaf06289_w_suffix04_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
