/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01675CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01675_w_weights26 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 78 leaf01675_w_segment26)
theorem leaf01675_w_weights26_identity : leaf01675_w_weights26=IntegerWeightedOuter.weights 12 1 128 78 leaf01675_w_segment26 := by decide +kernel
noncomputable def leaf01675_w_piece26 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01675_w_weights26 leaf01675_w_segment26)
theorem leaf01675_w_piece26_weighted : leaf01675_w_piece26=IntegerWeightedOuter.applyWeights leaf01675_w_weights26 leaf01675_w_segment26 := by decide +kernel
theorem leaf01675_w_piece26_identity : leaf01675_w_piece26=IntegerOuterTerms.transform 12 1 128 78 leaf01675_w_segment26 :=
  IntegerWeightedOuter.checked 12 1 128 78 leaf01675_w_segment26 leaf01675_w_piece26 leaf01675_w_weights26 leaf01675_w_weights26_identity leaf01675_w_piece26_weighted
#print axioms leaf01675_w_weights26_identity
#print axioms leaf01675_w_piece26_weighted
#print axioms leaf01675_w_piece26_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
