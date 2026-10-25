/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights20 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 60 leaf01260_w_segment20)
theorem leaf01260_w_weights20_identity : leaf01260_w_weights20=IntegerWeightedOuter.weights 8 1 16 60 leaf01260_w_segment20 := by decide +kernel
noncomputable def leaf01260_w_piece20 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights20 leaf01260_w_segment20)
theorem leaf01260_w_piece20_weighted : leaf01260_w_piece20=IntegerWeightedOuter.applyWeights leaf01260_w_weights20 leaf01260_w_segment20 := by decide +kernel
theorem leaf01260_w_piece20_identity : leaf01260_w_piece20=IntegerOuterTerms.transform 8 1 16 60 leaf01260_w_segment20 :=
  IntegerWeightedOuter.checked 8 1 16 60 leaf01260_w_segment20 leaf01260_w_piece20 leaf01260_w_weights20 leaf01260_w_weights20_identity leaf01260_w_piece20_weighted
#print axioms leaf01260_w_weights20_identity
#print axioms leaf01260_w_piece20_weighted
#print axioms leaf01260_w_piece20_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights21 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 63 leaf01260_w_segment21)
theorem leaf01260_w_weights21_identity : leaf01260_w_weights21=IntegerWeightedOuter.weights 8 1 16 63 leaf01260_w_segment21 := by decide +kernel
noncomputable def leaf01260_w_piece21 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights21 leaf01260_w_segment21)
theorem leaf01260_w_piece21_weighted : leaf01260_w_piece21=IntegerWeightedOuter.applyWeights leaf01260_w_weights21 leaf01260_w_segment21 := by decide +kernel
theorem leaf01260_w_piece21_identity : leaf01260_w_piece21=IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_segment21 :=
  IntegerWeightedOuter.checked 8 1 16 63 leaf01260_w_segment21 leaf01260_w_piece21 leaf01260_w_weights21 leaf01260_w_weights21_identity leaf01260_w_piece21_weighted
#print axioms leaf01260_w_weights21_identity
#print axioms leaf01260_w_piece21_weighted
#print axioms leaf01260_w_piece21_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights22 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 66 leaf01260_w_segment22)
theorem leaf01260_w_weights22_identity : leaf01260_w_weights22=IntegerWeightedOuter.weights 8 1 16 66 leaf01260_w_segment22 := by decide +kernel
noncomputable def leaf01260_w_piece22 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights22 leaf01260_w_segment22)
theorem leaf01260_w_piece22_weighted : leaf01260_w_piece22=IntegerWeightedOuter.applyWeights leaf01260_w_weights22 leaf01260_w_segment22 := by decide +kernel
theorem leaf01260_w_piece22_identity : leaf01260_w_piece22=IntegerOuterTerms.transform 8 1 16 66 leaf01260_w_segment22 :=
  IntegerWeightedOuter.checked 8 1 16 66 leaf01260_w_segment22 leaf01260_w_piece22 leaf01260_w_weights22 leaf01260_w_weights22_identity leaf01260_w_piece22_weighted
#print axioms leaf01260_w_weights22_identity
#print axioms leaf01260_w_piece22_weighted
#print axioms leaf01260_w_piece22_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights23 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 69 leaf01260_w_segment23)
theorem leaf01260_w_weights23_identity : leaf01260_w_weights23=IntegerWeightedOuter.weights 8 1 16 69 leaf01260_w_segment23 := by decide +kernel
noncomputable def leaf01260_w_piece23 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights23 leaf01260_w_segment23)
theorem leaf01260_w_piece23_weighted : leaf01260_w_piece23=IntegerWeightedOuter.applyWeights leaf01260_w_weights23 leaf01260_w_segment23 := by decide +kernel
theorem leaf01260_w_piece23_identity : leaf01260_w_piece23=IntegerOuterTerms.transform 8 1 16 69 leaf01260_w_segment23 :=
  IntegerWeightedOuter.checked 8 1 16 69 leaf01260_w_segment23 leaf01260_w_piece23 leaf01260_w_weights23 leaf01260_w_weights23_identity leaf01260_w_piece23_weighted
#print axioms leaf01260_w_weights23_identity
#print axioms leaf01260_w_piece23_weighted
#print axioms leaf01260_w_piece23_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights24 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 72 leaf01260_w_segment24)
theorem leaf01260_w_weights24_identity : leaf01260_w_weights24=IntegerWeightedOuter.weights 8 1 16 72 leaf01260_w_segment24 := by decide +kernel
noncomputable def leaf01260_w_piece24 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights24 leaf01260_w_segment24)
theorem leaf01260_w_piece24_weighted : leaf01260_w_piece24=IntegerWeightedOuter.applyWeights leaf01260_w_weights24 leaf01260_w_segment24 := by decide +kernel
theorem leaf01260_w_piece24_identity : leaf01260_w_piece24=IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_segment24 :=
  IntegerWeightedOuter.checked 8 1 16 72 leaf01260_w_segment24 leaf01260_w_piece24 leaf01260_w_weights24 leaf01260_w_weights24_identity leaf01260_w_piece24_weighted
#print axioms leaf01260_w_weights24_identity
#print axioms leaf01260_w_piece24_weighted
#print axioms leaf01260_w_piece24_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights25 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 75 leaf01260_w_segment25)
theorem leaf01260_w_weights25_identity : leaf01260_w_weights25=IntegerWeightedOuter.weights 8 1 16 75 leaf01260_w_segment25 := by decide +kernel
noncomputable def leaf01260_w_piece25 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights25 leaf01260_w_segment25)
theorem leaf01260_w_piece25_weighted : leaf01260_w_piece25=IntegerWeightedOuter.applyWeights leaf01260_w_weights25 leaf01260_w_segment25 := by decide +kernel
theorem leaf01260_w_piece25_identity : leaf01260_w_piece25=IntegerOuterTerms.transform 8 1 16 75 leaf01260_w_segment25 :=
  IntegerWeightedOuter.checked 8 1 16 75 leaf01260_w_segment25 leaf01260_w_piece25 leaf01260_w_weights25 leaf01260_w_weights25_identity leaf01260_w_piece25_weighted
#print axioms leaf01260_w_weights25_identity
#print axioms leaf01260_w_piece25_weighted
#print axioms leaf01260_w_piece25_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights26 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 78 leaf01260_w_segment26)
theorem leaf01260_w_weights26_identity : leaf01260_w_weights26=IntegerWeightedOuter.weights 8 1 16 78 leaf01260_w_segment26 := by decide +kernel
noncomputable def leaf01260_w_piece26 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights26 leaf01260_w_segment26)
theorem leaf01260_w_piece26_weighted : leaf01260_w_piece26=IntegerWeightedOuter.applyWeights leaf01260_w_weights26 leaf01260_w_segment26 := by decide +kernel
theorem leaf01260_w_piece26_identity : leaf01260_w_piece26=IntegerOuterTerms.transform 8 1 16 78 leaf01260_w_segment26 :=
  IntegerWeightedOuter.checked 8 1 16 78 leaf01260_w_segment26 leaf01260_w_piece26 leaf01260_w_weights26 leaf01260_w_weights26_identity leaf01260_w_piece26_weighted
#print axioms leaf01260_w_weights26_identity
#print axioms leaf01260_w_piece26_weighted
#print axioms leaf01260_w_piece26_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights27 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 81 leaf01260_w_segment27)
theorem leaf01260_w_weights27_identity : leaf01260_w_weights27=IntegerWeightedOuter.weights 8 1 16 81 leaf01260_w_segment27 := by decide +kernel
noncomputable def leaf01260_w_piece27 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights27 leaf01260_w_segment27)
theorem leaf01260_w_piece27_weighted : leaf01260_w_piece27=IntegerWeightedOuter.applyWeights leaf01260_w_weights27 leaf01260_w_segment27 := by decide +kernel
theorem leaf01260_w_piece27_identity : leaf01260_w_piece27=IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_segment27 :=
  IntegerWeightedOuter.checked 8 1 16 81 leaf01260_w_segment27 leaf01260_w_piece27 leaf01260_w_weights27 leaf01260_w_weights27_identity leaf01260_w_piece27_weighted
#print axioms leaf01260_w_weights27_identity
#print axioms leaf01260_w_piece27_weighted
#print axioms leaf01260_w_piece27_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights28 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 84 leaf01260_w_segment28)
theorem leaf01260_w_weights28_identity : leaf01260_w_weights28=IntegerWeightedOuter.weights 8 1 16 84 leaf01260_w_segment28 := by decide +kernel
noncomputable def leaf01260_w_piece28 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights28 leaf01260_w_segment28)
theorem leaf01260_w_piece28_weighted : leaf01260_w_piece28=IntegerWeightedOuter.applyWeights leaf01260_w_weights28 leaf01260_w_segment28 := by decide +kernel
theorem leaf01260_w_piece28_identity : leaf01260_w_piece28=IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_segment28 :=
  IntegerWeightedOuter.checked 8 1 16 84 leaf01260_w_segment28 leaf01260_w_piece28 leaf01260_w_weights28 leaf01260_w_weights28_identity leaf01260_w_piece28_weighted
#print axioms leaf01260_w_weights28_identity
#print axioms leaf01260_w_piece28_weighted
#print axioms leaf01260_w_piece28_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights29 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 87 leaf01260_w_segment29)
theorem leaf01260_w_weights29_identity : leaf01260_w_weights29=IntegerWeightedOuter.weights 8 1 16 87 leaf01260_w_segment29 := by decide +kernel
noncomputable def leaf01260_w_piece29 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights29 leaf01260_w_segment29)
theorem leaf01260_w_piece29_weighted : leaf01260_w_piece29=IntegerWeightedOuter.applyWeights leaf01260_w_weights29 leaf01260_w_segment29 := by decide +kernel
theorem leaf01260_w_piece29_identity : leaf01260_w_piece29=IntegerOuterTerms.transform 8 1 16 87 leaf01260_w_segment29 :=
  IntegerWeightedOuter.checked 8 1 16 87 leaf01260_w_segment29 leaf01260_w_piece29 leaf01260_w_weights29 leaf01260_w_weights29_identity leaf01260_w_piece29_weighted
#print axioms leaf01260_w_weights29_identity
#print axioms leaf01260_w_piece29_weighted
#print axioms leaf01260_w_piece29_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
