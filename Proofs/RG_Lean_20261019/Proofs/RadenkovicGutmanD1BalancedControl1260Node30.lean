/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node31
import Proofs.RadenkovicGutmanD1BalancedControl1260Node44
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value30 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input44.length) value31) value44)
theorem value30_join : value30=NestedInteger.add (NestedInteger.scale (16^input44.length) value31) value44 := by rfl
theorem value30_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value30) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 input30)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 45 66
    input31 input44 input30 value31 value44 value30
    (by decide +kernel) split30 value31_eval value44_eval value30_join x
#print axioms value30_join
#print axioms value30_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
