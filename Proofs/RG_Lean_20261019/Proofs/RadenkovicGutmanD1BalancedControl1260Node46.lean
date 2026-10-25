/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value46 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input48.length) DegreeOneLongClass00.leaf01260_w_piece22) DegreeOneLongClass00.leaf01260_w_piece23)
theorem value46_join : value46=NestedInteger.add (NestedInteger.scale (16^input48.length) DegreeOneLongClass00.leaf01260_w_piece22) DegreeOneLongClass00.leaf01260_w_piece23 := by rfl
theorem value46_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value46) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 input46)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 66 69
    input47 input48 input46 DegreeOneLongClass00.leaf01260_w_piece22 DegreeOneLongClass00.leaf01260_w_piece23 value46
    (by decide +kernel) split46 leaf47_eval leaf48_eval value46_join x
#print axioms value46_join
#print axioms value46_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
