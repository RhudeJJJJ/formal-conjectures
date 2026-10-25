/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece19
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join20
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix19 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source20.length) leaf06289_w_piece19) leaf06289_w_suffix20)
theorem leaf06289_w_suffix19_join : leaf06289_w_suffix19=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source20.length) leaf06289_w_piece19) leaf06289_w_suffix20 := by decide +kernel
theorem leaf06289_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 57 leaf06289_w_source19)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 57 60
    leaf06289_w_segment19 leaf06289_w_source20 leaf06289_w_source19
    leaf06289_w_piece19 leaf06289_w_suffix20 leaf06289_w_suffix19
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source19)
    leaf06289_w_piece19_identity leaf06289_w_suffix20_eval leaf06289_w_suffix19_join x
#print axioms leaf06289_w_suffix19_join
#print axioms leaf06289_w_suffix19_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
