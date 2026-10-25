/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node45
import Proofs.RadenkovicGutmanD1BalancedControl1260Node52
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value44 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input52.length) value45) value52)
theorem value44_join : value44=NestedInteger.add (NestedInteger.scale (16^input52.length) value45) value52 := by rfl
theorem value44_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value44) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 input44)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 66 78
    input45 input52 input44 value45 value52 value44
    (by decide +kernel) split44 value45_eval value52_eval value44_join x
#print axioms value44_join
#print axioms value44_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
