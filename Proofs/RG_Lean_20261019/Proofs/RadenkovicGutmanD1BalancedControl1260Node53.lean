/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value53 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input55.length) DegreeOneLongClass00.leaf01260_w_piece26) DegreeOneLongClass00.leaf01260_w_piece27)
theorem value53_join : value53=NestedInteger.add (NestedInteger.scale (16^input55.length) DegreeOneLongClass00.leaf01260_w_piece26) DegreeOneLongClass00.leaf01260_w_piece27 := by rfl
theorem value53_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value53) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 input53)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 78 81
    input54 input55 input53 DegreeOneLongClass00.leaf01260_w_piece26 DegreeOneLongClass00.leaf01260_w_piece27 value53
    (by decide +kernel) split53 leaf54_eval leaf55_eval value53_join x
#print axioms value53_join
#print axioms value53_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
