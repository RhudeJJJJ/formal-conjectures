/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01676CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01676_w_weights27 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 81 leaf01676_w_segment27)
theorem leaf01676_w_weights27_identity : leaf01676_w_weights27=IntegerWeightedOuter.weights 12 1 128 81 leaf01676_w_segment27 := by decide +kernel
noncomputable def leaf01676_w_piece27 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01676_w_weights27 leaf01676_w_segment27)
theorem leaf01676_w_piece27_weighted : leaf01676_w_piece27=IntegerWeightedOuter.applyWeights leaf01676_w_weights27 leaf01676_w_segment27 := by decide +kernel
theorem leaf01676_w_piece27_identity : leaf01676_w_piece27=IntegerOuterTerms.transform 12 1 128 81 leaf01676_w_segment27 :=
  IntegerWeightedOuter.checked 12 1 128 81 leaf01676_w_segment27 leaf01676_w_piece27 leaf01676_w_weights27 leaf01676_w_weights27_identity leaf01676_w_piece27_weighted
#print axioms leaf01676_w_weights27_identity
#print axioms leaf01676_w_piece27_weighted
#print axioms leaf01676_w_piece27_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
