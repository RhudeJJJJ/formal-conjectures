/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece00
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Join01
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source01.length) leaf06289_w_piece00) leaf06289_w_suffix01)
theorem leaf06289_w_affine_join : leaf06289_w_affine=NestedInteger.add (NestedInteger.scale (4096^leaf06289_w_source01.length) leaf06289_w_piece00) leaf06289_w_suffix01 := by decide +kernel
theorem leaf06289_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 0 leaf06289_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 4 1 4096 0 3
    leaf06289_w_segment00 leaf06289_w_source01 leaf06289_w_source00
    leaf06289_w_piece00 leaf06289_w_suffix01 leaf06289_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf06289_w_source00)
    leaf06289_w_piece00_identity leaf06289_w_suffix01_eval leaf06289_w_affine_join x
#print axioms leaf06289_w_affine_join
#print axioms leaf06289_w_affine_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
