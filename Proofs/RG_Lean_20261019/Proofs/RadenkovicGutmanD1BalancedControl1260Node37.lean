/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node38
import Proofs.RadenkovicGutmanD1BalancedControl1260Node41
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value37 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input41.length) value38) value41)
theorem value37_join : value37=NestedInteger.add (NestedInteger.scale (16^input41.length) value38) value41 := by rfl
theorem value37_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value37) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 input37)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 54 60
    input38 input41 input37 value38 value41 value37
    (by decide +kernel) split37 value38_eval value41_eval value37_join x
#print axioms value37_join
#print axioms value37_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
