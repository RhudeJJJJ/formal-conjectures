/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01306RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01306_w_weights27 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 14 1 32 81 leaf01306_w_segment27)
theorem leaf01306_w_weights27_identity : leaf01306_w_weights27=IntegerWeightedOuter.weights 14 1 32 81 leaf01306_w_segment27 := by decide +kernel
noncomputable def leaf01306_w_piece27 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01306_w_weights27 leaf01306_w_segment27)
theorem leaf01306_w_piece27_weighted : leaf01306_w_piece27=IntegerWeightedOuter.applyWeights leaf01306_w_weights27 leaf01306_w_segment27 := by decide +kernel
theorem leaf01306_w_piece27_identity : leaf01306_w_piece27=IntegerOuterTerms.transform 14 1 32 81 leaf01306_w_segment27 :=
  IntegerWeightedOuter.checked 14 1 32 81 leaf01306_w_segment27 leaf01306_w_piece27 leaf01306_w_weights27 leaf01306_w_weights27_identity leaf01306_w_piece27_weighted
#print axioms leaf01306_w_weights27_identity
#print axioms leaf01306_w_piece27_weighted
#print axioms leaf01306_w_piece27_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
