/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01679CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01679_w_weights05 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 15 leaf01679_w_segment05)
theorem leaf01679_w_weights05_identity : leaf01679_w_weights05=IntegerWeightedOuter.weights 12 1 128 15 leaf01679_w_segment05 := by decide +kernel
noncomputable def leaf01679_w_piece05 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01679_w_weights05 leaf01679_w_segment05)
theorem leaf01679_w_piece05_weighted : leaf01679_w_piece05=IntegerWeightedOuter.applyWeights leaf01679_w_weights05 leaf01679_w_segment05 := by decide +kernel
theorem leaf01679_w_piece05_identity : leaf01679_w_piece05=IntegerOuterTerms.transform 12 1 128 15 leaf01679_w_segment05 :=
  IntegerWeightedOuter.checked 12 1 128 15 leaf01679_w_segment05 leaf01679_w_piece05 leaf01679_w_weights05 leaf01679_w_weights05_identity leaf01679_w_piece05_weighted
#print axioms leaf01679_w_weights05_identity
#print axioms leaf01679_w_piece05_weighted
#print axioms leaf01679_w_piece05_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
