/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260GroupedCompositionalRepairPrepared
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_source00 : NestedInteger.Poly 3 := leaf01260_w_inner
noncomputable def leaf01260_w_segment00 : NestedInteger.Poly 3 := leaf01260_w_source00.take 3
noncomputable def leaf01260_w_source01 : NestedInteger.Poly 3 := leaf01260_w_source00.drop 3
noncomputable def leaf01260_w_segment01 : NestedInteger.Poly 3 := leaf01260_w_source01.take 3
noncomputable def leaf01260_w_source02 : NestedInteger.Poly 3 := leaf01260_w_source01.drop 3
noncomputable def leaf01260_w_segment02 : NestedInteger.Poly 3 := leaf01260_w_source02.take 3
noncomputable def leaf01260_w_source03 : NestedInteger.Poly 3 := leaf01260_w_source02.drop 3
noncomputable def leaf01260_w_segment03 : NestedInteger.Poly 3 := leaf01260_w_source03.take 3
noncomputable def leaf01260_w_source04 : NestedInteger.Poly 3 := leaf01260_w_source03.drop 3
noncomputable def leaf01260_w_segment04 : NestedInteger.Poly 3 := leaf01260_w_source04.take 3
noncomputable def leaf01260_w_source05 : NestedInteger.Poly 3 := leaf01260_w_source04.drop 3
noncomputable def leaf01260_w_segment05 : NestedInteger.Poly 3 := leaf01260_w_source05.take 3
noncomputable def leaf01260_w_source06 : NestedInteger.Poly 3 := leaf01260_w_source05.drop 3
noncomputable def leaf01260_w_segment06 : NestedInteger.Poly 3 := leaf01260_w_source06.take 3
noncomputable def leaf01260_w_source07 : NestedInteger.Poly 3 := leaf01260_w_source06.drop 3
noncomputable def leaf01260_w_segment07 : NestedInteger.Poly 3 := leaf01260_w_source07.take 3
noncomputable def leaf01260_w_source08 : NestedInteger.Poly 3 := leaf01260_w_source07.drop 3
noncomputable def leaf01260_w_segment08 : NestedInteger.Poly 3 := leaf01260_w_source08.take 3
noncomputable def leaf01260_w_source09 : NestedInteger.Poly 3 := leaf01260_w_source08.drop 3
noncomputable def leaf01260_w_segment09 : NestedInteger.Poly 3 := leaf01260_w_source09.take 3
noncomputable def leaf01260_w_source10 : NestedInteger.Poly 3 := leaf01260_w_source09.drop 3
noncomputable def leaf01260_w_segment10 : NestedInteger.Poly 3 := leaf01260_w_source10.take 3
noncomputable def leaf01260_w_source11 : NestedInteger.Poly 3 := leaf01260_w_source10.drop 3
noncomputable def leaf01260_w_segment11 : NestedInteger.Poly 3 := leaf01260_w_source11.take 3
noncomputable def leaf01260_w_source12 : NestedInteger.Poly 3 := leaf01260_w_source11.drop 3
noncomputable def leaf01260_w_segment12 : NestedInteger.Poly 3 := leaf01260_w_source12.take 3
noncomputable def leaf01260_w_source13 : NestedInteger.Poly 3 := leaf01260_w_source12.drop 3
noncomputable def leaf01260_w_segment13 : NestedInteger.Poly 3 := leaf01260_w_source13.take 3
noncomputable def leaf01260_w_source14 : NestedInteger.Poly 3 := leaf01260_w_source13.drop 3
noncomputable def leaf01260_w_segment14 : NestedInteger.Poly 3 := leaf01260_w_source14.take 3
noncomputable def leaf01260_w_source15 : NestedInteger.Poly 3 := leaf01260_w_source14.drop 3
noncomputable def leaf01260_w_segment15 : NestedInteger.Poly 3 := leaf01260_w_source15.take 3
noncomputable def leaf01260_w_source16 : NestedInteger.Poly 3 := leaf01260_w_source15.drop 3
noncomputable def leaf01260_w_segment16 : NestedInteger.Poly 3 := leaf01260_w_source16.take 3
noncomputable def leaf01260_w_source17 : NestedInteger.Poly 3 := leaf01260_w_source16.drop 3
noncomputable def leaf01260_w_segment17 : NestedInteger.Poly 3 := leaf01260_w_source17.take 3
noncomputable def leaf01260_w_source18 : NestedInteger.Poly 3 := leaf01260_w_source17.drop 3
noncomputable def leaf01260_w_segment18 : NestedInteger.Poly 3 := leaf01260_w_source18.take 3
noncomputable def leaf01260_w_source19 : NestedInteger.Poly 3 := leaf01260_w_source18.drop 3
noncomputable def leaf01260_w_segment19 : NestedInteger.Poly 3 := leaf01260_w_source19.take 3
noncomputable def leaf01260_w_source20 : NestedInteger.Poly 3 := leaf01260_w_source19.drop 3
noncomputable def leaf01260_w_segment20 : NestedInteger.Poly 3 := leaf01260_w_source20.take 3
noncomputable def leaf01260_w_source21 : NestedInteger.Poly 3 := leaf01260_w_source20.drop 3
noncomputable def leaf01260_w_segment21 : NestedInteger.Poly 3 := leaf01260_w_source21.take 3
noncomputable def leaf01260_w_source22 : NestedInteger.Poly 3 := leaf01260_w_source21.drop 3
noncomputable def leaf01260_w_segment22 : NestedInteger.Poly 3 := leaf01260_w_source22.take 3
noncomputable def leaf01260_w_source23 : NestedInteger.Poly 3 := leaf01260_w_source22.drop 3
noncomputable def leaf01260_w_segment23 : NestedInteger.Poly 3 := leaf01260_w_source23.take 3
noncomputable def leaf01260_w_source24 : NestedInteger.Poly 3 := leaf01260_w_source23.drop 3
noncomputable def leaf01260_w_segment24 : NestedInteger.Poly 3 := leaf01260_w_source24.take 3
noncomputable def leaf01260_w_source25 : NestedInteger.Poly 3 := leaf01260_w_source24.drop 3
noncomputable def leaf01260_w_segment25 : NestedInteger.Poly 3 := leaf01260_w_source25.take 3
noncomputable def leaf01260_w_source26 : NestedInteger.Poly 3 := leaf01260_w_source25.drop 3
noncomputable def leaf01260_w_segment26 : NestedInteger.Poly 3 := leaf01260_w_source26.take 3
noncomputable def leaf01260_w_source27 : NestedInteger.Poly 3 := leaf01260_w_source26.drop 3
noncomputable def leaf01260_w_segment27 : NestedInteger.Poly 3 := leaf01260_w_source27.take 3
noncomputable def leaf01260_w_source28 : NestedInteger.Poly 3 := leaf01260_w_source27.drop 3
noncomputable def leaf01260_w_segment28 : NestedInteger.Poly 3 := leaf01260_w_source28.take 3
noncomputable def leaf01260_w_source29 : NestedInteger.Poly 3 := leaf01260_w_source28.drop 3
noncomputable def leaf01260_w_segment29 : NestedInteger.Poly 3 := leaf01260_w_source29.take 3
#print axioms leaf01260_inner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights00 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 0 leaf01260_w_segment00)
theorem leaf01260_w_weights00_identity : leaf01260_w_weights00=IntegerWeightedOuter.weights 8 1 16 0 leaf01260_w_segment00 := by decide +kernel
noncomputable def leaf01260_w_piece00 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights00 leaf01260_w_segment00)
theorem leaf01260_w_piece00_weighted : leaf01260_w_piece00=IntegerWeightedOuter.applyWeights leaf01260_w_weights00 leaf01260_w_segment00 := by decide +kernel
theorem leaf01260_w_piece00_identity : leaf01260_w_piece00=IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_segment00 :=
  IntegerWeightedOuter.checked 8 1 16 0 leaf01260_w_segment00 leaf01260_w_piece00 leaf01260_w_weights00 leaf01260_w_weights00_identity leaf01260_w_piece00_weighted
#print axioms leaf01260_w_weights00_identity
#print axioms leaf01260_w_piece00_weighted
#print axioms leaf01260_w_piece00_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights01 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 3 leaf01260_w_segment01)
theorem leaf01260_w_weights01_identity : leaf01260_w_weights01=IntegerWeightedOuter.weights 8 1 16 3 leaf01260_w_segment01 := by decide +kernel
noncomputable def leaf01260_w_piece01 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights01 leaf01260_w_segment01)
theorem leaf01260_w_piece01_weighted : leaf01260_w_piece01=IntegerWeightedOuter.applyWeights leaf01260_w_weights01 leaf01260_w_segment01 := by decide +kernel
theorem leaf01260_w_piece01_identity : leaf01260_w_piece01=IntegerOuterTerms.transform 8 1 16 3 leaf01260_w_segment01 :=
  IntegerWeightedOuter.checked 8 1 16 3 leaf01260_w_segment01 leaf01260_w_piece01 leaf01260_w_weights01 leaf01260_w_weights01_identity leaf01260_w_piece01_weighted
#print axioms leaf01260_w_weights01_identity
#print axioms leaf01260_w_piece01_weighted
#print axioms leaf01260_w_piece01_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights02 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 6 leaf01260_w_segment02)
theorem leaf01260_w_weights02_identity : leaf01260_w_weights02=IntegerWeightedOuter.weights 8 1 16 6 leaf01260_w_segment02 := by decide +kernel
noncomputable def leaf01260_w_piece02 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights02 leaf01260_w_segment02)
theorem leaf01260_w_piece02_weighted : leaf01260_w_piece02=IntegerWeightedOuter.applyWeights leaf01260_w_weights02 leaf01260_w_segment02 := by decide +kernel
theorem leaf01260_w_piece02_identity : leaf01260_w_piece02=IntegerOuterTerms.transform 8 1 16 6 leaf01260_w_segment02 :=
  IntegerWeightedOuter.checked 8 1 16 6 leaf01260_w_segment02 leaf01260_w_piece02 leaf01260_w_weights02 leaf01260_w_weights02_identity leaf01260_w_piece02_weighted
#print axioms leaf01260_w_weights02_identity
#print axioms leaf01260_w_piece02_weighted
#print axioms leaf01260_w_piece02_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights03 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 9 leaf01260_w_segment03)
theorem leaf01260_w_weights03_identity : leaf01260_w_weights03=IntegerWeightedOuter.weights 8 1 16 9 leaf01260_w_segment03 := by decide +kernel
noncomputable def leaf01260_w_piece03 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights03 leaf01260_w_segment03)
theorem leaf01260_w_piece03_weighted : leaf01260_w_piece03=IntegerWeightedOuter.applyWeights leaf01260_w_weights03 leaf01260_w_segment03 := by decide +kernel
theorem leaf01260_w_piece03_identity : leaf01260_w_piece03=IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_segment03 :=
  IntegerWeightedOuter.checked 8 1 16 9 leaf01260_w_segment03 leaf01260_w_piece03 leaf01260_w_weights03 leaf01260_w_weights03_identity leaf01260_w_piece03_weighted
#print axioms leaf01260_w_weights03_identity
#print axioms leaf01260_w_piece03_weighted
#print axioms leaf01260_w_piece03_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights04 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 12 leaf01260_w_segment04)
theorem leaf01260_w_weights04_identity : leaf01260_w_weights04=IntegerWeightedOuter.weights 8 1 16 12 leaf01260_w_segment04 := by decide +kernel
noncomputable def leaf01260_w_piece04 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights04 leaf01260_w_segment04)
theorem leaf01260_w_piece04_weighted : leaf01260_w_piece04=IntegerWeightedOuter.applyWeights leaf01260_w_weights04 leaf01260_w_segment04 := by decide +kernel
theorem leaf01260_w_piece04_identity : leaf01260_w_piece04=IntegerOuterTerms.transform 8 1 16 12 leaf01260_w_segment04 :=
  IntegerWeightedOuter.checked 8 1 16 12 leaf01260_w_segment04 leaf01260_w_piece04 leaf01260_w_weights04 leaf01260_w_weights04_identity leaf01260_w_piece04_weighted
#print axioms leaf01260_w_weights04_identity
#print axioms leaf01260_w_piece04_weighted
#print axioms leaf01260_w_piece04_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights05 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 15 leaf01260_w_segment05)
theorem leaf01260_w_weights05_identity : leaf01260_w_weights05=IntegerWeightedOuter.weights 8 1 16 15 leaf01260_w_segment05 := by decide +kernel
noncomputable def leaf01260_w_piece05 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights05 leaf01260_w_segment05)
theorem leaf01260_w_piece05_weighted : leaf01260_w_piece05=IntegerWeightedOuter.applyWeights leaf01260_w_weights05 leaf01260_w_segment05 := by decide +kernel
theorem leaf01260_w_piece05_identity : leaf01260_w_piece05=IntegerOuterTerms.transform 8 1 16 15 leaf01260_w_segment05 :=
  IntegerWeightedOuter.checked 8 1 16 15 leaf01260_w_segment05 leaf01260_w_piece05 leaf01260_w_weights05 leaf01260_w_weights05_identity leaf01260_w_piece05_weighted
#print axioms leaf01260_w_weights05_identity
#print axioms leaf01260_w_piece05_weighted
#print axioms leaf01260_w_piece05_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights06 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 18 leaf01260_w_segment06)
theorem leaf01260_w_weights06_identity : leaf01260_w_weights06=IntegerWeightedOuter.weights 8 1 16 18 leaf01260_w_segment06 := by decide +kernel
noncomputable def leaf01260_w_piece06 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights06 leaf01260_w_segment06)
theorem leaf01260_w_piece06_weighted : leaf01260_w_piece06=IntegerWeightedOuter.applyWeights leaf01260_w_weights06 leaf01260_w_segment06 := by decide +kernel
theorem leaf01260_w_piece06_identity : leaf01260_w_piece06=IntegerOuterTerms.transform 8 1 16 18 leaf01260_w_segment06 :=
  IntegerWeightedOuter.checked 8 1 16 18 leaf01260_w_segment06 leaf01260_w_piece06 leaf01260_w_weights06 leaf01260_w_weights06_identity leaf01260_w_piece06_weighted
#print axioms leaf01260_w_weights06_identity
#print axioms leaf01260_w_piece06_weighted
#print axioms leaf01260_w_piece06_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights07 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 21 leaf01260_w_segment07)
theorem leaf01260_w_weights07_identity : leaf01260_w_weights07=IntegerWeightedOuter.weights 8 1 16 21 leaf01260_w_segment07 := by decide +kernel
noncomputable def leaf01260_w_piece07 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights07 leaf01260_w_segment07)
theorem leaf01260_w_piece07_weighted : leaf01260_w_piece07=IntegerWeightedOuter.applyWeights leaf01260_w_weights07 leaf01260_w_segment07 := by decide +kernel
theorem leaf01260_w_piece07_identity : leaf01260_w_piece07=IntegerOuterTerms.transform 8 1 16 21 leaf01260_w_segment07 :=
  IntegerWeightedOuter.checked 8 1 16 21 leaf01260_w_segment07 leaf01260_w_piece07 leaf01260_w_weights07 leaf01260_w_weights07_identity leaf01260_w_piece07_weighted
#print axioms leaf01260_w_weights07_identity
#print axioms leaf01260_w_piece07_weighted
#print axioms leaf01260_w_piece07_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights08 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 24 leaf01260_w_segment08)
theorem leaf01260_w_weights08_identity : leaf01260_w_weights08=IntegerWeightedOuter.weights 8 1 16 24 leaf01260_w_segment08 := by decide +kernel
noncomputable def leaf01260_w_piece08 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights08 leaf01260_w_segment08)
theorem leaf01260_w_piece08_weighted : leaf01260_w_piece08=IntegerWeightedOuter.applyWeights leaf01260_w_weights08 leaf01260_w_segment08 := by decide +kernel
theorem leaf01260_w_piece08_identity : leaf01260_w_piece08=IntegerOuterTerms.transform 8 1 16 24 leaf01260_w_segment08 :=
  IntegerWeightedOuter.checked 8 1 16 24 leaf01260_w_segment08 leaf01260_w_piece08 leaf01260_w_weights08 leaf01260_w_weights08_identity leaf01260_w_piece08_weighted
#print axioms leaf01260_w_weights08_identity
#print axioms leaf01260_w_piece08_weighted
#print axioms leaf01260_w_piece08_identity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_weights09 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 27 leaf01260_w_segment09)
theorem leaf01260_w_weights09_identity : leaf01260_w_weights09=IntegerWeightedOuter.weights 8 1 16 27 leaf01260_w_segment09 := by decide +kernel
noncomputable def leaf01260_w_piece09 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights09 leaf01260_w_segment09)
theorem leaf01260_w_piece09_weighted : leaf01260_w_piece09=IntegerWeightedOuter.applyWeights leaf01260_w_weights09 leaf01260_w_segment09 := by decide +kernel
theorem leaf01260_w_piece09_identity : leaf01260_w_piece09=IntegerOuterTerms.transform 8 1 16 27 leaf01260_w_segment09 :=
  IntegerWeightedOuter.checked 8 1 16 27 leaf01260_w_segment09 leaf01260_w_piece09 leaf01260_w_weights09 leaf01260_w_weights09_identity leaf01260_w_piece09_weighted
#print axioms leaf01260_w_weights09_identity
#print axioms leaf01260_w_piece09_weighted
#print axioms leaf01260_w_piece09_identity
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
