/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece21
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join22
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix21 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source22.length) leaf06289_w_piece21) leaf06289_w_suffix22)
theorem leaf06289_w_suffix21_join : leaf06289_w_suffix21=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source22.length) leaf06289_w_piece21) leaf06289_w_suffix22 := by decide +kernel
theorem leaf06289_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 63 leaf06289_w_source21)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 63 66
    leaf06289_w_segment21 leaf06289_w_source22 leaf06289_w_source21
    leaf06289_w_piece21 leaf06289_w_suffix22 leaf06289_w_suffix21
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source21)
    leaf06289_w_piece21_identity leaf06289_w_suffix22_eval leaf06289_w_suffix21_join x
#print axioms leaf06289_w_suffix21_join
#print axioms leaf06289_w_suffix21_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
