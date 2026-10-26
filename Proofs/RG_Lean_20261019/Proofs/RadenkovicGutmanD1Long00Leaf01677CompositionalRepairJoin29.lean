/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01677CompositionalRepairPiece29
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01677_w_suffix29 : NestedInteger.Poly 3 := leaf01677_w_piece29
theorem leaf01677_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01677_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 87 leaf01677_w_source29)) x := by
  have h : leaf01677_w_segment29=leaf01677_w_source29 := by decide +kernel
  rw [leaf01677_w_suffix29,leaf01677_w_piece29_identity,h]
#print axioms leaf01677_w_suffix29_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
