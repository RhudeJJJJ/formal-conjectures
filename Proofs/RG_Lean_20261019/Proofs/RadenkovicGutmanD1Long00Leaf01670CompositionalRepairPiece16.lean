/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01670CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01670_w_weights16 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 48 leaf01670_w_segment16)
theorem leaf01670_w_weights16_identity : leaf01670_w_weights16=IntegerWeightedOuter.weights 12 1 128 48 leaf01670_w_segment16 := by decide +kernel
noncomputable def leaf01670_w_piece16 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01670_w_weights16 leaf01670_w_segment16)
theorem leaf01670_w_piece16_weighted : leaf01670_w_piece16=IntegerWeightedOuter.applyWeights leaf01670_w_weights16 leaf01670_w_segment16 := by decide +kernel
theorem leaf01670_w_piece16_identity : leaf01670_w_piece16=IntegerOuterTerms.transform 12 1 128 48 leaf01670_w_segment16 :=
  IntegerWeightedOuter.checked 12 1 128 48 leaf01670_w_segment16 leaf01670_w_piece16 leaf01670_w_weights16 leaf01670_w_weights16_identity leaf01670_w_piece16_weighted
#print axioms leaf01670_w_weights16_identity
#print axioms leaf01670_w_piece16_weighted
#print axioms leaf01670_w_piece16_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
