/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value17 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input19.length) DegreeOneLongClass00.leaf01260_w_piece07) DegreeOneLongClass00.leaf01260_w_piece08)
theorem value17_join : value17=NestedInteger.add (NestedInteger.scale (16^input19.length) DegreeOneLongClass00.leaf01260_w_piece07) DegreeOneLongClass00.leaf01260_w_piece08 := by rfl
theorem value17_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value17) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 input17)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 21 24
    input18 input19 input17 DegreeOneLongClass00.leaf01260_w_piece07 DegreeOneLongClass00.leaf01260_w_piece08 value17
    (by decide +kernel) split17 leaf18_eval leaf19_eval value17_join x
#print axioms value17_join
#print axioms value17_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
