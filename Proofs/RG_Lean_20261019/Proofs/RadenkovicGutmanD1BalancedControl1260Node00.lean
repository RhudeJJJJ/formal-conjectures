/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node01
import Proofs.RadenkovicGutmanD1BalancedControl1260Node30
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value00 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input30.length) value01) value30)
theorem value00_join : value00=NestedInteger.add (NestedInteger.scale (16^input30.length) value01) value30 := by rfl
theorem value00_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value00) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 input00)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 0 45
    input01 input30 input00 value01 value30 value00
    (by decide +kernel) split00 value01_eval value30_eval value00_join x
#print axioms value00_join
#print axioms value00_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
