/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01617CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01617_w_weights08 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 128 24 leaf01617_w_segment08)
theorem leaf01617_w_weights08_identity : leaf01617_w_weights08=IntegerWeightedOuter.weights 15 1 128 24 leaf01617_w_segment08 := by decide +kernel
noncomputable def leaf01617_w_piece08 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01617_w_weights08 leaf01617_w_segment08)
theorem leaf01617_w_piece08_weighted : leaf01617_w_piece08=IntegerWeightedOuter.applyWeights leaf01617_w_weights08 leaf01617_w_segment08 := by decide +kernel
theorem leaf01617_w_piece08_identity : leaf01617_w_piece08=IntegerOuterTerms.transform 15 1 128 24 leaf01617_w_segment08 :=
  IntegerWeightedOuter.checked 15 1 128 24 leaf01617_w_segment08 leaf01617_w_piece08 leaf01617_w_weights08 leaf01617_w_weights08_identity leaf01617_w_piece08_weighted
#print axioms leaf01617_w_weights08_identity
#print axioms leaf01617_w_piece08_weighted
#print axioms leaf01617_w_piece08_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
