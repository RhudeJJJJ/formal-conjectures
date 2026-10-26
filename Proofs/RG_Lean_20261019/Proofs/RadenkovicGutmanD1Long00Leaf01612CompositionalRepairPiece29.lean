/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01612_w_weights29 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 128 87 leaf01612_w_segment29)
theorem leaf01612_w_weights29_identity : leaf01612_w_weights29=IntegerWeightedOuter.weights 16 1 128 87 leaf01612_w_segment29 := by decide +kernel
noncomputable def leaf01612_w_piece29 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01612_w_weights29 leaf01612_w_segment29)
theorem leaf01612_w_piece29_weighted : leaf01612_w_piece29=IntegerWeightedOuter.applyWeights leaf01612_w_weights29 leaf01612_w_segment29 := by decide +kernel
theorem leaf01612_w_piece29_identity : leaf01612_w_piece29=IntegerOuterTerms.transform 16 1 128 87 leaf01612_w_segment29 :=
  IntegerWeightedOuter.checked 16 1 128 87 leaf01612_w_segment29 leaf01612_w_piece29 leaf01612_w_weights29 leaf01612_w_weights29_identity leaf01612_w_piece29_weighted
#print axioms leaf01612_w_weights29_identity
#print axioms leaf01612_w_piece29_weighted
#print axioms leaf01612_w_piece29_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
