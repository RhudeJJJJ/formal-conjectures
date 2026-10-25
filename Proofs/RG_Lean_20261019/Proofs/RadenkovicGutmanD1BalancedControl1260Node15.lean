/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node16
import Proofs.RadenkovicGutmanD1BalancedControl1260Node23
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value15 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input23.length) value16) value23)
theorem value15_join : value15=NestedInteger.add (NestedInteger.scale (16^input23.length) value16) value23 := by rfl
theorem value15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value15) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 input15)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 21 33
    input16 input23 input15 value16 value23 value15
    (by decide +kernel) split15 value16_eval value23_eval value15_join x
#print axioms value15_join
#print axioms value15_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
