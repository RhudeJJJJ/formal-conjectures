/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node02
import Proofs.RadenkovicGutmanD1BalancedControl1260Node15
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input15.length) value02) value15)
theorem value01_join : value01=NestedInteger.add (NestedInteger.scale (16^input15.length) value02) value15 := by rfl
theorem value01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value01) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 input01)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 0 21
    input02 input15 input01 value02 value15 value01
    (by decide +kernel) split01 value02_eval value15_eval value01_join x
#print axioms value01_join
#print axioms value01_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
