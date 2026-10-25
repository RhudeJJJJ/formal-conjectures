/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
import Proofs.RadenkovicGutmanD1BalancedControl1260Node34
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value32 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input34.length) DegreeOneLongClass00.leaf01260_w_piece15) value34)
theorem value32_join : value32=NestedInteger.add (NestedInteger.scale (16^input34.length) DegreeOneLongClass00.leaf01260_w_piece15) value34 := by rfl
theorem value32_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value32) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 input32)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 45 48
    input33 input34 input32 DegreeOneLongClass00.leaf01260_w_piece15 value34 value32
    (by decide +kernel) split32 leaf33_eval value34_eval value32_join x
#print axioms value32_join
#print axioms value32_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
