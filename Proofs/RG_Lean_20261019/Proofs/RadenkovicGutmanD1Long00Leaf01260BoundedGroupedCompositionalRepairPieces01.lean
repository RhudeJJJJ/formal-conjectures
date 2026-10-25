/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights10 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 30 leaf01260_w_segment10)
theorem leaf01260_w_weights10_identity : leaf01260_w_weights10=IntegerWeightedOuter.weights 8 1 16 30 leaf01260_w_segment10 := by decide +kernel
noncomputable def leaf01260_w_piece10 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights10 leaf01260_w_segment10)
theorem leaf01260_w_piece10_weighted : leaf01260_w_piece10=IntegerWeightedOuter.applyWeights leaf01260_w_weights10 leaf01260_w_segment10 := by decide +kernel
theorem leaf01260_w_piece10_identity : leaf01260_w_piece10=IntegerOuterTerms.transform 8 1 16 30 leaf01260_w_segment10 :=
  IntegerWeightedOuter.checked 8 1 16 30 leaf01260_w_segment10 leaf01260_w_piece10 leaf01260_w_weights10 leaf01260_w_weights10_identity leaf01260_w_piece10_weighted
#print axioms leaf01260_w_weights10_identity
#print axioms leaf01260_w_piece10_weighted
#print axioms leaf01260_w_piece10_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights11 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 33 leaf01260_w_segment11)
theorem leaf01260_w_weights11_identity : leaf01260_w_weights11=IntegerWeightedOuter.weights 8 1 16 33 leaf01260_w_segment11 := by decide +kernel
noncomputable def leaf01260_w_piece11 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights11 leaf01260_w_segment11)
theorem leaf01260_w_piece11_weighted : leaf01260_w_piece11=IntegerWeightedOuter.applyWeights leaf01260_w_weights11 leaf01260_w_segment11 := by decide +kernel
theorem leaf01260_w_piece11_identity : leaf01260_w_piece11=IntegerOuterTerms.transform 8 1 16 33 leaf01260_w_segment11 :=
  IntegerWeightedOuter.checked 8 1 16 33 leaf01260_w_segment11 leaf01260_w_piece11 leaf01260_w_weights11 leaf01260_w_weights11_identity leaf01260_w_piece11_weighted
#print axioms leaf01260_w_weights11_identity
#print axioms leaf01260_w_piece11_weighted
#print axioms leaf01260_w_piece11_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights12 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 36 leaf01260_w_segment12)
theorem leaf01260_w_weights12_identity : leaf01260_w_weights12=IntegerWeightedOuter.weights 8 1 16 36 leaf01260_w_segment12 := by decide +kernel
noncomputable def leaf01260_w_piece12 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights12 leaf01260_w_segment12)
theorem leaf01260_w_piece12_weighted : leaf01260_w_piece12=IntegerWeightedOuter.applyWeights leaf01260_w_weights12 leaf01260_w_segment12 := by decide +kernel
theorem leaf01260_w_piece12_identity : leaf01260_w_piece12=IntegerOuterTerms.transform 8 1 16 36 leaf01260_w_segment12 :=
  IntegerWeightedOuter.checked 8 1 16 36 leaf01260_w_segment12 leaf01260_w_piece12 leaf01260_w_weights12 leaf01260_w_weights12_identity leaf01260_w_piece12_weighted
#print axioms leaf01260_w_weights12_identity
#print axioms leaf01260_w_piece12_weighted
#print axioms leaf01260_w_piece12_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights13 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 39 leaf01260_w_segment13)
theorem leaf01260_w_weights13_identity : leaf01260_w_weights13=IntegerWeightedOuter.weights 8 1 16 39 leaf01260_w_segment13 := by decide +kernel
noncomputable def leaf01260_w_piece13 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights13 leaf01260_w_segment13)
theorem leaf01260_w_piece13_weighted : leaf01260_w_piece13=IntegerWeightedOuter.applyWeights leaf01260_w_weights13 leaf01260_w_segment13 := by decide +kernel
theorem leaf01260_w_piece13_identity : leaf01260_w_piece13=IntegerOuterTerms.transform 8 1 16 39 leaf01260_w_segment13 :=
  IntegerWeightedOuter.checked 8 1 16 39 leaf01260_w_segment13 leaf01260_w_piece13 leaf01260_w_weights13 leaf01260_w_weights13_identity leaf01260_w_piece13_weighted
#print axioms leaf01260_w_weights13_identity
#print axioms leaf01260_w_piece13_weighted
#print axioms leaf01260_w_piece13_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights14 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 42 leaf01260_w_segment14)
theorem leaf01260_w_weights14_identity : leaf01260_w_weights14=IntegerWeightedOuter.weights 8 1 16 42 leaf01260_w_segment14 := by decide +kernel
noncomputable def leaf01260_w_piece14 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights14 leaf01260_w_segment14)
theorem leaf01260_w_piece14_weighted : leaf01260_w_piece14=IntegerWeightedOuter.applyWeights leaf01260_w_weights14 leaf01260_w_segment14 := by decide +kernel
theorem leaf01260_w_piece14_identity : leaf01260_w_piece14=IntegerOuterTerms.transform 8 1 16 42 leaf01260_w_segment14 :=
  IntegerWeightedOuter.checked 8 1 16 42 leaf01260_w_segment14 leaf01260_w_piece14 leaf01260_w_weights14 leaf01260_w_weights14_identity leaf01260_w_piece14_weighted
#print axioms leaf01260_w_weights14_identity
#print axioms leaf01260_w_piece14_weighted
#print axioms leaf01260_w_piece14_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights15 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 45 leaf01260_w_segment15)
theorem leaf01260_w_weights15_identity : leaf01260_w_weights15=IntegerWeightedOuter.weights 8 1 16 45 leaf01260_w_segment15 := by decide +kernel
noncomputable def leaf01260_w_piece15 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights15 leaf01260_w_segment15)
theorem leaf01260_w_piece15_weighted : leaf01260_w_piece15=IntegerWeightedOuter.applyWeights leaf01260_w_weights15 leaf01260_w_segment15 := by decide +kernel
theorem leaf01260_w_piece15_identity : leaf01260_w_piece15=IntegerOuterTerms.transform 8 1 16 45 leaf01260_w_segment15 :=
  IntegerWeightedOuter.checked 8 1 16 45 leaf01260_w_segment15 leaf01260_w_piece15 leaf01260_w_weights15 leaf01260_w_weights15_identity leaf01260_w_piece15_weighted
#print axioms leaf01260_w_weights15_identity
#print axioms leaf01260_w_piece15_weighted
#print axioms leaf01260_w_piece15_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights16 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 48 leaf01260_w_segment16)
theorem leaf01260_w_weights16_identity : leaf01260_w_weights16=IntegerWeightedOuter.weights 8 1 16 48 leaf01260_w_segment16 := by decide +kernel
noncomputable def leaf01260_w_piece16 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights16 leaf01260_w_segment16)
theorem leaf01260_w_piece16_weighted : leaf01260_w_piece16=IntegerWeightedOuter.applyWeights leaf01260_w_weights16 leaf01260_w_segment16 := by decide +kernel
theorem leaf01260_w_piece16_identity : leaf01260_w_piece16=IntegerOuterTerms.transform 8 1 16 48 leaf01260_w_segment16 :=
  IntegerWeightedOuter.checked 8 1 16 48 leaf01260_w_segment16 leaf01260_w_piece16 leaf01260_w_weights16 leaf01260_w_weights16_identity leaf01260_w_piece16_weighted
#print axioms leaf01260_w_weights16_identity
#print axioms leaf01260_w_piece16_weighted
#print axioms leaf01260_w_piece16_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights17 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 51 leaf01260_w_segment17)
theorem leaf01260_w_weights17_identity : leaf01260_w_weights17=IntegerWeightedOuter.weights 8 1 16 51 leaf01260_w_segment17 := by decide +kernel
noncomputable def leaf01260_w_piece17 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights17 leaf01260_w_segment17)
theorem leaf01260_w_piece17_weighted : leaf01260_w_piece17=IntegerWeightedOuter.applyWeights leaf01260_w_weights17 leaf01260_w_segment17 := by decide +kernel
theorem leaf01260_w_piece17_identity : leaf01260_w_piece17=IntegerOuterTerms.transform 8 1 16 51 leaf01260_w_segment17 :=
  IntegerWeightedOuter.checked 8 1 16 51 leaf01260_w_segment17 leaf01260_w_piece17 leaf01260_w_weights17 leaf01260_w_weights17_identity leaf01260_w_piece17_weighted
#print axioms leaf01260_w_weights17_identity
#print axioms leaf01260_w_piece17_weighted
#print axioms leaf01260_w_piece17_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights18 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 54 leaf01260_w_segment18)
theorem leaf01260_w_weights18_identity : leaf01260_w_weights18=IntegerWeightedOuter.weights 8 1 16 54 leaf01260_w_segment18 := by decide +kernel
noncomputable def leaf01260_w_piece18 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights18 leaf01260_w_segment18)
theorem leaf01260_w_piece18_weighted : leaf01260_w_piece18=IntegerWeightedOuter.applyWeights leaf01260_w_weights18 leaf01260_w_segment18 := by decide +kernel
theorem leaf01260_w_piece18_identity : leaf01260_w_piece18=IntegerOuterTerms.transform 8 1 16 54 leaf01260_w_segment18 :=
  IntegerWeightedOuter.checked 8 1 16 54 leaf01260_w_segment18 leaf01260_w_piece18 leaf01260_w_weights18 leaf01260_w_weights18_identity leaf01260_w_piece18_weighted
#print axioms leaf01260_w_weights18_identity
#print axioms leaf01260_w_piece18_weighted
#print axioms leaf01260_w_piece18_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights19 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 57 leaf01260_w_segment19)
theorem leaf01260_w_weights19_identity : leaf01260_w_weights19=IntegerWeightedOuter.weights 8 1 16 57 leaf01260_w_segment19 := by decide +kernel
noncomputable def leaf01260_w_piece19 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights19 leaf01260_w_segment19)
theorem leaf01260_w_piece19_weighted : leaf01260_w_piece19=IntegerWeightedOuter.applyWeights leaf01260_w_weights19 leaf01260_w_segment19 := by decide +kernel
theorem leaf01260_w_piece19_identity : leaf01260_w_piece19=IntegerOuterTerms.transform 8 1 16 57 leaf01260_w_segment19 :=
  IntegerWeightedOuter.checked 8 1 16 57 leaf01260_w_segment19 leaf01260_w_piece19 leaf01260_w_weights19 leaf01260_w_weights19_identity leaf01260_w_piece19_weighted
#print axioms leaf01260_w_weights19_identity
#print axioms leaf01260_w_piece19_weighted
#print axioms leaf01260_w_piece19_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
