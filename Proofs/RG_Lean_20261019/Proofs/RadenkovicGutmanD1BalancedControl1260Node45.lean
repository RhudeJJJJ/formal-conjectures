/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node46
import Proofs.RadenkovicGutmanD1BalancedControl1260Node49
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value45 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input49.length) value46) value49)
theorem value45_join : value45=NestedInteger.add (NestedInteger.scale (16^input49.length) value46) value49 := by rfl
theorem value45_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value45) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 input45)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 66 72
    input46 input49 input45 value46 value49 value45
    (by decide +kernel) split45 value46_eval value49_eval value45_join x
#print axioms value45_join
#print axioms value45_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
