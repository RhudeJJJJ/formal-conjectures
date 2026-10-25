/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value41 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input43.length) DegreeOneLongClass00.leaf01260_w_piece20) DegreeOneLongClass00.leaf01260_w_piece21)
theorem value41_join : value41=NestedInteger.add (NestedInteger.scale (16^input43.length) DegreeOneLongClass00.leaf01260_w_piece20) DegreeOneLongClass00.leaf01260_w_piece21 := by rfl
theorem value41_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value41) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 60 input41)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 60 63
    input42 input43 input41 DegreeOneLongClass00.leaf01260_w_piece20 DegreeOneLongClass00.leaf01260_w_piece21 value41
    (by decide +kernel) split41 leaf42_eval leaf43_eval value41_join x
#print axioms value41_join
#print axioms value41_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
