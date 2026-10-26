/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01679CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01679_w_weights12 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 36 leaf01679_w_segment12)
theorem leaf01679_w_weights12_identity : leaf01679_w_weights12=IntegerWeightedOuter.weights 12 1 128 36 leaf01679_w_segment12 := by decide +kernel
noncomputable def leaf01679_w_piece12 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01679_w_weights12 leaf01679_w_segment12)
theorem leaf01679_w_piece12_weighted : leaf01679_w_piece12=IntegerWeightedOuter.applyWeights leaf01679_w_weights12 leaf01679_w_segment12 := by decide +kernel
theorem leaf01679_w_piece12_identity : leaf01679_w_piece12=IntegerOuterTerms.transform 12 1 128 36 leaf01679_w_segment12 :=
  IntegerWeightedOuter.checked 12 1 128 36 leaf01679_w_segment12 leaf01679_w_piece12 leaf01679_w_weights12 leaf01679_w_weights12_identity leaf01679_w_piece12_weighted
#print axioms leaf01679_w_weights12_identity
#print axioms leaf01679_w_piece12_weighted
#print axioms leaf01679_w_piece12_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
