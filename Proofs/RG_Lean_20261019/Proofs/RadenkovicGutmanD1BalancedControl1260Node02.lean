/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node03
import Proofs.RadenkovicGutmanD1BalancedControl1260Node08
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value02 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input08.length) value03) value08)
theorem value02_join : value02=NestedInteger.add (NestedInteger.scale (16^input08.length) value03) value08 := by rfl
theorem value02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value02) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 input02)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 0 9
    input03 input08 input02 value03 value08 value02
    (by decide +kernel) split02 value03_eval value08_eval value02_join x
#print axioms value02_join
#print axioms value02_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
