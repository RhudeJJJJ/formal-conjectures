/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01616CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01616_w_weights25 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 128 75 leaf01616_w_segment25)
theorem leaf01616_w_weights25_identity : leaf01616_w_weights25=IntegerWeightedOuter.weights 15 1 128 75 leaf01616_w_segment25 := by decide +kernel
noncomputable def leaf01616_w_piece25 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01616_w_weights25 leaf01616_w_segment25)
theorem leaf01616_w_piece25_weighted : leaf01616_w_piece25=IntegerWeightedOuter.applyWeights leaf01616_w_weights25 leaf01616_w_segment25 := by decide +kernel
theorem leaf01616_w_piece25_identity : leaf01616_w_piece25=IntegerOuterTerms.transform 15 1 128 75 leaf01616_w_segment25 :=
  IntegerWeightedOuter.checked 15 1 128 75 leaf01616_w_segment25 leaf01616_w_piece25 leaf01616_w_weights25 leaf01616_w_weights25_identity leaf01616_w_piece25_weighted
#print axioms leaf01616_w_weights25_identity
#print axioms leaf01616_w_piece25_weighted
#print axioms leaf01616_w_piece25_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
