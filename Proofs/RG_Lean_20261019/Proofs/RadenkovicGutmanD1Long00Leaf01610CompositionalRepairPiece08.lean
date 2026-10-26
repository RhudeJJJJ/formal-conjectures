/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01610CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01610_w_weights08 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 128 24 leaf01610_w_segment08)
theorem leaf01610_w_weights08_identity : leaf01610_w_weights08=IntegerWeightedOuter.weights 16 1 128 24 leaf01610_w_segment08 := by decide +kernel
noncomputable def leaf01610_w_piece08 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01610_w_weights08 leaf01610_w_segment08)
theorem leaf01610_w_piece08_weighted : leaf01610_w_piece08=IntegerWeightedOuter.applyWeights leaf01610_w_weights08 leaf01610_w_segment08 := by decide +kernel
theorem leaf01610_w_piece08_identity : leaf01610_w_piece08=IntegerOuterTerms.transform 16 1 128 24 leaf01610_w_segment08 :=
  IntegerWeightedOuter.checked 16 1 128 24 leaf01610_w_segment08 leaf01610_w_piece08 leaf01610_w_weights08 leaf01610_w_weights08_identity leaf01610_w_piece08_weighted
#print axioms leaf01610_w_weights08_identity
#print axioms leaf01610_w_piece08_weighted
#print axioms leaf01610_w_piece08_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
