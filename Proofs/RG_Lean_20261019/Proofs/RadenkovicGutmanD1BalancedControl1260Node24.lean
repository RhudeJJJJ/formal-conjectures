/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value24 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input26.length) DegreeOneLongClass00.leaf01260_w_piece11) DegreeOneLongClass00.leaf01260_w_piece12)
theorem value24_join : value24=NestedInteger.add (NestedInteger.scale (16^input26.length) DegreeOneLongClass00.leaf01260_w_piece11) DegreeOneLongClass00.leaf01260_w_piece12 := by rfl
theorem value24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value24) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 input24)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 33 36
    input25 input26 input24 DegreeOneLongClass00.leaf01260_w_piece11 DegreeOneLongClass00.leaf01260_w_piece12 value24
    (by decide +kernel) split24 leaf25_eval leaf26_eval value24_join x
#print axioms value24_join
#print axioms value24_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
