/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node17
import Proofs.RadenkovicGutmanD1BalancedControl1260Node20
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value16 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input20.length) value17) value20)
theorem value16_join : value16=NestedInteger.add (NestedInteger.scale (16^input20.length) value17) value20 := by rfl
theorem value16_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value16) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 input16)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 21 27
    input17 input20 input16 value17 value20 value16
    (by decide +kernel) split16 value17_eval value20_eval value16_join x
#print axioms value16_join
#print axioms value16_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
