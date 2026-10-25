/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node05
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value03 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input05.length) DegreeOneLongClass00.leaf01260_w_piece00) value05)
theorem value03_join : value03=NestedInteger.add (NestedInteger.scale (16^input05.length) DegreeOneLongClass00.leaf01260_w_piece00) value05 := by rfl
theorem value03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value03) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 input03)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 0 3
    input04 input05 input03 DegreeOneLongClass00.leaf01260_w_piece00 value05 value03
    (by decide +kernel) split03 leaf04_eval value05_eval value03_join x
#print axioms value03_join
#print axioms value03_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
