/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input22.length) DegreeOneLongClass00.leaf01260_w_piece09) DegreeOneLongClass00.leaf01260_w_piece10)
theorem value20_join : value20=NestedInteger.add (NestedInteger.scale (16^input22.length) DegreeOneLongClass00.leaf01260_w_piece09) DegreeOneLongClass00.leaf01260_w_piece10 := by rfl
theorem value20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value20) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 27 input20)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 27 30
    input21 input22 input20 DegreeOneLongClass00.leaf01260_w_piece09 DegreeOneLongClass00.leaf01260_w_piece10 value20
    (by decide +kernel) split20 leaf21_eval leaf22_eval value20_join x
#print axioms value20_join
#print axioms value20_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
