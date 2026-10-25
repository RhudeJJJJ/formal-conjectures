/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00SegmentedIntegerLeaf00935Piece29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_suffix29 : NestedInteger.Poly 3 := leaf00935_w_piece29
theorem leaf00935_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00935_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 2 1 2048 87 leaf00935_w_source29)) x := by
  have h : leaf00935_w_segment29=leaf00935_w_source29 := by decide +kernel
  rw [leaf00935_w_suffix29,leaf00935_w_piece29_identity,h]
#print axioms leaf00935_w_suffix29_eval
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
