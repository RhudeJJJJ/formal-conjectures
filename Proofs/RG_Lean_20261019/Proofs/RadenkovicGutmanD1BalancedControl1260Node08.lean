/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node09
import Proofs.RadenkovicGutmanD1BalancedControl1260Node12
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value08 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input12.length) value09) value12)
theorem value08_join : value08=NestedInteger.add (NestedInteger.scale (16^input12.length) value09) value12 := by rfl
theorem value08_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value08) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 input08)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 9 15
    input09 input12 input08 value09 value12 value08
    (by decide +kernel) split08 value09_eval value12_eval value08_join x
#print axioms value08_join
#print axioms value08_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
