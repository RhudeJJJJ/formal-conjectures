/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node32
import Proofs.RadenkovicGutmanD1BalancedControl1260Node37
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value31 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input37.length) value32) value37)
theorem value31_join : value31=NestedInteger.add (NestedInteger.scale (16^input37.length) value32) value37 := by rfl
theorem value31_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value31) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 input31)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 45 54
    input32 input37 input31 value32 value37 value31
    (by decide +kernel) split31 value32_eval value37_eval value31_join x
#print axioms value31_join
#print axioms value31_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
