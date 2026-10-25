/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value38 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input40.length) DegreeOneLongClass00.leaf01260_w_piece18) DegreeOneLongClass00.leaf01260_w_piece19)
theorem value38_join : value38=NestedInteger.add (NestedInteger.scale (16^input40.length) DegreeOneLongClass00.leaf01260_w_piece18) DegreeOneLongClass00.leaf01260_w_piece19 := by rfl
theorem value38_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value38) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 input38)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 54 57
    input39 input40 input38 DegreeOneLongClass00.leaf01260_w_piece18 DegreeOneLongClass00.leaf01260_w_piece19 value38
    (by decide +kernel) split38 leaf39_eval leaf40_eval value38_join x
#print axioms value38_join
#print axioms value38_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
