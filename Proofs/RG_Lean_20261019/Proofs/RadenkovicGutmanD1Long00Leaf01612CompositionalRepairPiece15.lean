/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01612_w_weights15 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 128 45 leaf01612_w_segment15)
theorem leaf01612_w_weights15_identity : leaf01612_w_weights15=IntegerWeightedOuter.weights 16 1 128 45 leaf01612_w_segment15 := by decide +kernel
noncomputable def leaf01612_w_piece15 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01612_w_weights15 leaf01612_w_segment15)
theorem leaf01612_w_piece15_weighted : leaf01612_w_piece15=IntegerWeightedOuter.applyWeights leaf01612_w_weights15 leaf01612_w_segment15 := by decide +kernel
theorem leaf01612_w_piece15_identity : leaf01612_w_piece15=IntegerOuterTerms.transform 16 1 128 45 leaf01612_w_segment15 :=
  IntegerWeightedOuter.checked 16 1 128 45 leaf01612_w_segment15 leaf01612_w_piece15 leaf01612_w_weights15 leaf01612_w_weights15_identity leaf01612_w_piece15_weighted
#print axioms leaf01612_w_weights15_identity
#print axioms leaf01612_w_piece15_weighted
#print axioms leaf01612_w_piece15_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
