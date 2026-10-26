/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01671CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01671_w_weights07 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 21 leaf01671_w_segment07)
theorem leaf01671_w_weights07_identity : leaf01671_w_weights07=IntegerWeightedOuter.weights 12 1 128 21 leaf01671_w_segment07 := by decide +kernel
noncomputable def leaf01671_w_piece07 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01671_w_weights07 leaf01671_w_segment07)
theorem leaf01671_w_piece07_weighted : leaf01671_w_piece07=IntegerWeightedOuter.applyWeights leaf01671_w_weights07 leaf01671_w_segment07 := by decide +kernel
theorem leaf01671_w_piece07_identity : leaf01671_w_piece07=IntegerOuterTerms.transform 12 1 128 21 leaf01671_w_segment07 :=
  IntegerWeightedOuter.checked 12 1 128 21 leaf01671_w_segment07 leaf01671_w_piece07 leaf01671_w_weights07 leaf01671_w_weights07_identity leaf01671_w_piece07_weighted
#print axioms leaf01671_w_weights07_identity
#print axioms leaf01671_w_piece07_weighted
#print axioms leaf01671_w_piece07_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
