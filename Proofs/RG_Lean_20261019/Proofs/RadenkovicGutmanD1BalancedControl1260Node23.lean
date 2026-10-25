/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node24
import Proofs.RadenkovicGutmanD1BalancedControl1260Node27
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value23 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input27.length) value24) value27)
theorem value23_join : value23=NestedInteger.add (NestedInteger.scale (16^input27.length) value24) value27 := by rfl
theorem value23_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value23) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 input23)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 33 39
    input24 input27 input23 value24 value27 value23
    (by decide +kernel) split23 value24_eval value27_eval value23_join x
#print axioms value23_join
#print axioms value23_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
