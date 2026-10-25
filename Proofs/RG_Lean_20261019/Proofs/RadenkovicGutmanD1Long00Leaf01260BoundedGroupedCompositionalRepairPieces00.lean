/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
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
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
