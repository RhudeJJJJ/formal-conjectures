/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01446RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01446_w_weights27 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 64 81 leaf01446_w_segment27)
theorem leaf01446_w_weights27_identity : leaf01446_w_weights27=IntegerWeightedOuter.weights 15 1 64 81 leaf01446_w_segment27 := by decide +kernel
noncomputable def leaf01446_w_piece27 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01446_w_weights27 leaf01446_w_segment27)
theorem leaf01446_w_piece27_weighted : leaf01446_w_piece27=IntegerWeightedOuter.applyWeights leaf01446_w_weights27 leaf01446_w_segment27 := by decide +kernel
theorem leaf01446_w_piece27_identity : leaf01446_w_piece27=IntegerOuterTerms.transform 15 1 64 81 leaf01446_w_segment27 :=
  IntegerWeightedOuter.checked 15 1 64 81 leaf01446_w_segment27 leaf01446_w_piece27 leaf01446_w_weights27 leaf01446_w_weights27_identity leaf01446_w_piece27_weighted
#print axioms leaf01446_w_weights27_identity
#print axioms leaf01446_w_piece27_weighted
#print axioms leaf01446_w_piece27_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
