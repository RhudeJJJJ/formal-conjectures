/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input29.length) DegreeOneLongClass00.leaf01260_w_piece13) DegreeOneLongClass00.leaf01260_w_piece14)
theorem value27_join : value27=NestedInteger.add (NestedInteger.scale (16^input29.length) DegreeOneLongClass00.leaf01260_w_piece13) DegreeOneLongClass00.leaf01260_w_piece14 := by rfl
theorem value27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value27) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 39 input27)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 39 42
    input28 input29 input27 DegreeOneLongClass00.leaf01260_w_piece13 DegreeOneLongClass00.leaf01260_w_piece14 value27
    (by decide +kernel) split27 leaf28_eval leaf29_eval value27_join x
#print axioms value27_join
#print axioms value27_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
