/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01615CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01615_w_weights00 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 128 0 leaf01615_w_segment00)
theorem leaf01615_w_weights00_identity : leaf01615_w_weights00=IntegerWeightedOuter.weights 15 1 128 0 leaf01615_w_segment00 := by decide +kernel
noncomputable def leaf01615_w_piece00 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01615_w_weights00 leaf01615_w_segment00)
theorem leaf01615_w_piece00_weighted : leaf01615_w_piece00=IntegerWeightedOuter.applyWeights leaf01615_w_weights00 leaf01615_w_segment00 := by decide +kernel
theorem leaf01615_w_piece00_identity : leaf01615_w_piece00=IntegerOuterTerms.transform 15 1 128 0 leaf01615_w_segment00 :=
  IntegerWeightedOuter.checked 15 1 128 0 leaf01615_w_segment00 leaf01615_w_piece00 leaf01615_w_weights00 leaf01615_w_weights00_identity leaf01615_w_piece00_weighted
#print axioms leaf01615_w_weights00_identity
#print axioms leaf01615_w_piece00_weighted
#print axioms leaf01615_w_piece00_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
