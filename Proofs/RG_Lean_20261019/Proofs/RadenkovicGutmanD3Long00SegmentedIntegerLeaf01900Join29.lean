/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00SegmentedIntegerLeaf01900Piece29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_suffix29 : NestedInteger.Poly 3 := leaf01900_w_piece29
theorem leaf01900_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01900_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 559 3 12800 87 leaf01900_w_source29)) x := by
  have h : leaf01900_w_segment29=leaf01900_w_source29 := by decide +kernel
  rw [leaf01900_w_suffix29,leaf01900_w_piece29_identity,h]
#print axioms leaf01900_w_suffix29_eval
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
