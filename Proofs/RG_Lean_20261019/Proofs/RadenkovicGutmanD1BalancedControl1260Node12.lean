/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value12 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input14.length) DegreeOneLongClass00.leaf01260_w_piece05) DegreeOneLongClass00.leaf01260_w_piece06)
theorem value12_join : value12=NestedInteger.add (NestedInteger.scale (16^input14.length) DegreeOneLongClass00.leaf01260_w_piece05) DegreeOneLongClass00.leaf01260_w_piece06 := by rfl
theorem value12_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value12) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 15 input12)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 15 18
    input13 input14 input12 DegreeOneLongClass00.leaf01260_w_piece05 DegreeOneLongClass00.leaf01260_w_piece06 value12
    (by decide +kernel) split12 leaf13_eval leaf14_eval value12_join x
#print axioms value12_join
#print axioms value12_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
