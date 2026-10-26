/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01616CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01616_w_weights21 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 128 63 leaf01616_w_segment21)
theorem leaf01616_w_weights21_identity : leaf01616_w_weights21=IntegerWeightedOuter.weights 15 1 128 63 leaf01616_w_segment21 := by decide +kernel
noncomputable def leaf01616_w_piece21 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01616_w_weights21 leaf01616_w_segment21)
theorem leaf01616_w_piece21_weighted : leaf01616_w_piece21=IntegerWeightedOuter.applyWeights leaf01616_w_weights21 leaf01616_w_segment21 := by decide +kernel
theorem leaf01616_w_piece21_identity : leaf01616_w_piece21=IntegerOuterTerms.transform 15 1 128 63 leaf01616_w_segment21 :=
  IntegerWeightedOuter.checked 15 1 128 63 leaf01616_w_segment21 leaf01616_w_piece21 leaf01616_w_weights21 leaf01616_w_weights21_identity leaf01616_w_piece21_weighted
#print axioms leaf01616_w_weights21_identity
#print axioms leaf01616_w_piece21_weighted
#print axioms leaf01616_w_piece21_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
