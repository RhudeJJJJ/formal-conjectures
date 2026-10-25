/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node53
import Proofs.RadenkovicGutmanD1BalancedControl1260Node56
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value52 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input56.length) value53) value56)
theorem value52_join : value52=NestedInteger.add (NestedInteger.scale (16^input56.length) value53) value56 := by rfl
theorem value52_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value52) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 input52)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 78 84
    input53 input56 input52 value53 value56 value52
    (by decide +kernel) split52 value53_eval value56_eval value52_join x
#print axioms value52_join
#print axioms value52_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
