/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Piece29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_suffix29 : NestedInteger.Poly 3 := leaf00023_w_piece29
theorem leaf00023_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00023_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 27 1 3200 87 leaf00023_w_source29)) x := by
  have h : leaf00023_w_segment29=leaf00023_w_source29 := by decide +kernel
  rw [leaf00023_w_suffix29,leaf00023_w_piece29_identity,h]
#print axioms leaf00023_w_suffix29_eval
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
