/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece03
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join04
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix03 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source04.length) leaf06289_w_piece03) leaf06289_w_suffix04)
theorem leaf06289_w_suffix03_join : leaf06289_w_suffix03=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source04.length) leaf06289_w_piece03) leaf06289_w_suffix04 := by decide +kernel
theorem leaf06289_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 9 leaf06289_w_source03)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 9 12
    leaf06289_w_segment03 leaf06289_w_source04 leaf06289_w_source03
    leaf06289_w_piece03 leaf06289_w_suffix04 leaf06289_w_suffix03
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source03)
    leaf06289_w_piece03_identity leaf06289_w_suffix04_eval leaf06289_w_suffix03_join x
#print axioms leaf06289_w_suffix03_join
#print axioms leaf06289_w_suffix03_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
