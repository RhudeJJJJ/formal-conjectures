/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Complete
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def leaf01260_w_affine : NestedInteger.Poly 3 := D1BalancedControl1260.value00
theorem leaf01260_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_affine) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_source00)) x :=
  D1BalancedControl1260.original_inner_transform_eval x
#print axioms leaf01260_w_affine_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
