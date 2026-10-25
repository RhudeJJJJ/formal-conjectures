/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Piece29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_suffix29 : NestedInteger.Poly 3 := leaf06289_w_piece29
theorem leaf06289_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf06289_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 4 1 4096 87 leaf06289_w_source29)) x := by
  have h : leaf06289_w_segment29=leaf06289_w_source29 := by decide +kernel
  rw [leaf06289_w_suffix29,leaf06289_w_piece29_identity,h]
#print axioms leaf06289_w_suffix29_eval
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
