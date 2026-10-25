/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00SegmentedIntegerLeaf06289Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_weights04 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 12 leaf06289_w_segment04)
theorem leaf06289_w_weights04_identity : leaf06289_w_weights04=IntegerWeightedOuter.weights 4 1 4096 12 leaf06289_w_segment04 := by decide +kernel
noncomputable def leaf06289_w_piece04 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf06289_w_weights04 leaf06289_w_segment04)
theorem leaf06289_w_piece04_weighted : leaf06289_w_piece04=IntegerWeightedOuter.applyWeights leaf06289_w_weights04 leaf06289_w_segment04 := by decide +kernel
theorem leaf06289_w_piece04_identity : leaf06289_w_piece04=IntegerOuterTerms.transform 4 1 4096 12 leaf06289_w_segment04 :=
  IntegerWeightedOuter.checked 4 1 4096 12 leaf06289_w_segment04 leaf06289_w_piece04 leaf06289_w_weights04 leaf06289_w_weights04_identity leaf06289_w_piece04_weighted
#print axioms leaf06289_w_weights04_identity
#print axioms leaf06289_w_piece04_weighted
#print axioms leaf06289_w_piece04_identity
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
