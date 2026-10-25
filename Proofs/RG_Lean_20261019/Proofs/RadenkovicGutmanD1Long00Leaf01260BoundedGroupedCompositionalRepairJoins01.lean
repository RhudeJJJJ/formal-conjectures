/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairPieces01
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairJoins00
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix19 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source20.length) leaf01260_w_piece19) leaf01260_w_suffix20)
theorem leaf01260_w_suffix19_join : leaf01260_w_suffix19=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source20.length) leaf01260_w_piece19) leaf01260_w_suffix20 := by decide +kernel
theorem leaf01260_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 57 leaf01260_w_source19)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 57 60
    leaf01260_w_segment19 leaf01260_w_source20 leaf01260_w_source19
    leaf01260_w_piece19 leaf01260_w_suffix20 leaf01260_w_suffix19
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source19)
    leaf01260_w_piece19_identity leaf01260_w_suffix20_eval leaf01260_w_suffix19_join x
#print axioms leaf01260_w_suffix19_join
#print axioms leaf01260_w_suffix19_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix18 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source19.length) leaf01260_w_piece18) leaf01260_w_suffix19)
theorem leaf01260_w_suffix18_join : leaf01260_w_suffix18=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source19.length) leaf01260_w_piece18) leaf01260_w_suffix19 := by decide +kernel
theorem leaf01260_w_suffix18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix18) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 leaf01260_w_source18)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 54 57
    leaf01260_w_segment18 leaf01260_w_source19 leaf01260_w_source18
    leaf01260_w_piece18 leaf01260_w_suffix19 leaf01260_w_suffix18
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source18)
    leaf01260_w_piece18_identity leaf01260_w_suffix19_eval leaf01260_w_suffix18_join x
#print axioms leaf01260_w_suffix18_join
#print axioms leaf01260_w_suffix18_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix17 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source18.length) leaf01260_w_piece17) leaf01260_w_suffix18)
theorem leaf01260_w_suffix17_join : leaf01260_w_suffix17=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source18.length) leaf01260_w_piece17) leaf01260_w_suffix18 := by decide +kernel
theorem leaf01260_w_suffix17_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix17) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 leaf01260_w_source17)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 51 54
    leaf01260_w_segment17 leaf01260_w_source18 leaf01260_w_source17
    leaf01260_w_piece17 leaf01260_w_suffix18 leaf01260_w_suffix17
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source17)
    leaf01260_w_piece17_identity leaf01260_w_suffix18_eval leaf01260_w_suffix17_join x
#print axioms leaf01260_w_suffix17_join
#print axioms leaf01260_w_suffix17_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix16 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source17.length) leaf01260_w_piece16) leaf01260_w_suffix17)
theorem leaf01260_w_suffix16_join : leaf01260_w_suffix16=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source17.length) leaf01260_w_piece16) leaf01260_w_suffix17 := by decide +kernel
theorem leaf01260_w_suffix16_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix16) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 leaf01260_w_source16)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 48 51
    leaf01260_w_segment16 leaf01260_w_source17 leaf01260_w_source16
    leaf01260_w_piece16 leaf01260_w_suffix17 leaf01260_w_suffix16
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source16)
    leaf01260_w_piece16_identity leaf01260_w_suffix17_eval leaf01260_w_suffix16_join x
#print axioms leaf01260_w_suffix16_join
#print axioms leaf01260_w_suffix16_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix15 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source16.length) leaf01260_w_piece15) leaf01260_w_suffix16)
theorem leaf01260_w_suffix15_join : leaf01260_w_suffix15=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source16.length) leaf01260_w_piece15) leaf01260_w_suffix16 := by decide +kernel
theorem leaf01260_w_suffix15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix15) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 leaf01260_w_source15)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 45 48
    leaf01260_w_segment15 leaf01260_w_source16 leaf01260_w_source15
    leaf01260_w_piece15 leaf01260_w_suffix16 leaf01260_w_suffix15
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source15)
    leaf01260_w_piece15_identity leaf01260_w_suffix16_eval leaf01260_w_suffix15_join x
#print axioms leaf01260_w_suffix15_join
#print axioms leaf01260_w_suffix15_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix14 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source15.length) leaf01260_w_piece14) leaf01260_w_suffix15)
theorem leaf01260_w_suffix14_join : leaf01260_w_suffix14=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source15.length) leaf01260_w_piece14) leaf01260_w_suffix15 := by decide +kernel
theorem leaf01260_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 leaf01260_w_source14)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 42 45
    leaf01260_w_segment14 leaf01260_w_source15 leaf01260_w_source14
    leaf01260_w_piece14 leaf01260_w_suffix15 leaf01260_w_suffix14
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source14)
    leaf01260_w_piece14_identity leaf01260_w_suffix15_eval leaf01260_w_suffix14_join x
#print axioms leaf01260_w_suffix14_join
#print axioms leaf01260_w_suffix14_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix13 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source14.length) leaf01260_w_piece13) leaf01260_w_suffix14)
theorem leaf01260_w_suffix13_join : leaf01260_w_suffix13=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source14.length) leaf01260_w_piece13) leaf01260_w_suffix14 := by decide +kernel
theorem leaf01260_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 39 leaf01260_w_source13)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 39 42
    leaf01260_w_segment13 leaf01260_w_source14 leaf01260_w_source13
    leaf01260_w_piece13 leaf01260_w_suffix14 leaf01260_w_suffix13
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source13)
    leaf01260_w_piece13_identity leaf01260_w_suffix14_eval leaf01260_w_suffix13_join x
#print axioms leaf01260_w_suffix13_join
#print axioms leaf01260_w_suffix13_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix12 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source13.length) leaf01260_w_piece12) leaf01260_w_suffix13)
theorem leaf01260_w_suffix12_join : leaf01260_w_suffix12=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source13.length) leaf01260_w_piece12) leaf01260_w_suffix13 := by decide +kernel
theorem leaf01260_w_suffix12_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix12) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 36 leaf01260_w_source12)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 36 39
    leaf01260_w_segment12 leaf01260_w_source13 leaf01260_w_source12
    leaf01260_w_piece12 leaf01260_w_suffix13 leaf01260_w_suffix12
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source12)
    leaf01260_w_piece12_identity leaf01260_w_suffix13_eval leaf01260_w_suffix12_join x
#print axioms leaf01260_w_suffix12_join
#print axioms leaf01260_w_suffix12_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix11 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source12.length) leaf01260_w_piece11) leaf01260_w_suffix12)
theorem leaf01260_w_suffix11_join : leaf01260_w_suffix11=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source12.length) leaf01260_w_piece11) leaf01260_w_suffix12 := by decide +kernel
theorem leaf01260_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 leaf01260_w_source11)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 33 36
    leaf01260_w_segment11 leaf01260_w_source12 leaf01260_w_source11
    leaf01260_w_piece11 leaf01260_w_suffix12 leaf01260_w_suffix11
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source11)
    leaf01260_w_piece11_identity leaf01260_w_suffix12_eval leaf01260_w_suffix11_join x
#print axioms leaf01260_w_suffix11_join
#print axioms leaf01260_w_suffix11_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix10 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source11.length) leaf01260_w_piece10) leaf01260_w_suffix11)
theorem leaf01260_w_suffix10_join : leaf01260_w_suffix10=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source11.length) leaf01260_w_piece10) leaf01260_w_suffix11 := by decide +kernel
theorem leaf01260_w_suffix10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix10) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 30 leaf01260_w_source10)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 30 33
    leaf01260_w_segment10 leaf01260_w_source11 leaf01260_w_source10
    leaf01260_w_piece10 leaf01260_w_suffix11 leaf01260_w_suffix10
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source10)
    leaf01260_w_piece10_identity leaf01260_w_suffix11_eval leaf01260_w_suffix10_join x
#print axioms leaf01260_w_suffix10_join
#print axioms leaf01260_w_suffix10_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
