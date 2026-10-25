/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value56 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input58.length) DegreeOneLongClass00.leaf01260_w_piece28) DegreeOneLongClass00.leaf01260_w_piece29)
theorem value56_join : value56=NestedInteger.add (NestedInteger.scale (16^input58.length) DegreeOneLongClass00.leaf01260_w_piece28) DegreeOneLongClass00.leaf01260_w_piece29 := by rfl
theorem value56_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value56) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 input56)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 84 87
    input57 input58 input56 DegreeOneLongClass00.leaf01260_w_piece28 DegreeOneLongClass00.leaf01260_w_piece29 value56
    (by decide +kernel) split56 leaf57_eval leaf58_eval value56_join x
#print axioms value56_join
#print axioms value56_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
