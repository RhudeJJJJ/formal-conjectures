/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Node00
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem original_inner_transform_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value00) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 DegreeOneLongClass00.leaf01260_w_source00)) x := value00_eval x
#print axioms original_inner_transform_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
