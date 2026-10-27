/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01279RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01279_w_weights09 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 32 27 leaf01279_w_segment09)
theorem leaf01279_w_weights09_identity : leaf01279_w_weights09=IntegerWeightedOuter.weights 15 1 32 27 leaf01279_w_segment09 := by decide +kernel
noncomputable def leaf01279_w_piece09 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01279_w_weights09 leaf01279_w_segment09)
theorem leaf01279_w_piece09_weighted : leaf01279_w_piece09=IntegerWeightedOuter.applyWeights leaf01279_w_weights09 leaf01279_w_segment09 := by decide +kernel
theorem leaf01279_w_piece09_identity : leaf01279_w_piece09=IntegerOuterTerms.transform 15 1 32 27 leaf01279_w_segment09 :=
  IntegerWeightedOuter.checked 15 1 32 27 leaf01279_w_segment09 leaf01279_w_piece09 leaf01279_w_weights09 leaf01279_w_weights09_identity leaf01279_w_piece09_weighted
#print axioms leaf01279_w_weights09_identity
#print axioms leaf01279_w_piece09_weighted
#print axioms leaf01279_w_piece09_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
