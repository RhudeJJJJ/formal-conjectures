/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1BalancedControl1260Inputs
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluationBoth
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def value49 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^input51.length) DegreeOneLongClass00.leaf01260_w_piece24) DegreeOneLongClass00.leaf01260_w_piece25)
theorem value49_join : value49=NestedInteger.add (NestedInteger.scale (16^input51.length) DegreeOneLongClass00.leaf01260_w_piece24) DegreeOneLongClass00.leaf01260_w_piece25 := by rfl
theorem value49_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 value49) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 input49)) x :=
  IntegerOuterJoinedEvaluationBoth.joined 8 1 16 72 75
    input50 input51 input49 DegreeOneLongClass00.leaf01260_w_piece24 DegreeOneLongClass00.leaf01260_w_piece25 value49
    (by decide +kernel) split49 leaf50_eval leaf51_eval value49_join x
#print axioms value49_join
#print axioms value49_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
