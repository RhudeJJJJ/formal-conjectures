/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value34 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input36.length) DegreeOneLongClass00.leaf01260_w_piece16) DegreeOneLongClass00.leaf01260_w_piece17)
theorem value34_join : value34=NestedInteger.add (NestedInteger.scale (16^input36.length) DegreeOneLongClass00.leaf01260_w_piece16) DegreeOneLongClass00.leaf01260_w_piece17 := by rfl
theorem value34_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value34) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 input34)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 48 51
    input35 input36 input34 DegreeOneLongClass00.leaf01260_w_piece16 DegreeOneLongClass00.leaf01260_w_piece17 value34
    (by decide +kernel) split34 leaf35_eval leaf36_eval value34_join x
#print axioms value34_join
#print axioms value34_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
