/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value05 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input07.length) DegreeOneLongClass00.leaf01260_w_piece01) DegreeOneLongClass00.leaf01260_w_piece02)
theorem value05_join : value05=NestedInteger.add (NestedInteger.scale (16^input07.length) DegreeOneLongClass00.leaf01260_w_piece01) DegreeOneLongClass00.leaf01260_w_piece02 := by rfl
theorem value05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value05) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 3 input05)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 3 6
    input06 input07 input05 DegreeOneLongClass00.leaf01260_w_piece01 DegreeOneLongClass00.leaf01260_w_piece02 value05
    (by decide +kernel) split05 leaf06_eval leaf07_eval value05_join x
#print axioms value05_join
#print axioms value05_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
