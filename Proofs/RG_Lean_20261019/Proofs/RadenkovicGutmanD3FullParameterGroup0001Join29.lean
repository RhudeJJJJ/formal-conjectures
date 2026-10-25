/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0001Piece29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00004_w_suffix29 : NestedInteger.Poly 3 := leaf00004_w_piece29
theorem leaf00004_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00004_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 33 1 32000 87 leaf00004_w_source29)) x := by
  have h : leaf00004_w_segment29=leaf00004_w_source29 := by decide +kernel
  rw [leaf00004_w_suffix29,leaf00004_w_piece29_identity,h]
#print axioms leaf00004_w_suffix29_eval
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
