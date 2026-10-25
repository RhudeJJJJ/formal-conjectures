/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input11.length) DegreeOneLongClass00.leaf01260_w_piece03) DegreeOneLongClass00.leaf01260_w_piece04)
theorem value09_join : value09=NestedInteger.add (NestedInteger.scale (16^input11.length) DegreeOneLongClass00.leaf01260_w_piece03) DegreeOneLongClass00.leaf01260_w_piece04 := by rfl
theorem value09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value09) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 input09)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 9 12
    input10 input11 input09 DegreeOneLongClass00.leaf01260_w_piece03 DegreeOneLongClass00.leaf01260_w_piece04 value09
    (by decide +kernel) split09 leaf10_eval leaf11_eval value09_join x
#print axioms value09_join
#print axioms value09_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
