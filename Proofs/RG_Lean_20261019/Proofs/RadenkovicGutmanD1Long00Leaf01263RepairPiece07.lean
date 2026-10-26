/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01263RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01263_w_weights07 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 21 leaf01263_w_segment07)
theorem leaf01263_w_weights07_identity : leaf01263_w_weights07=IntegerWeightedOuter.weights 8 1 16 21 leaf01263_w_segment07 := by decide +kernel
noncomputable def leaf01263_w_piece07 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01263_w_weights07 leaf01263_w_segment07)
theorem leaf01263_w_piece07_weighted : leaf01263_w_piece07=IntegerWeightedOuter.applyWeights leaf01263_w_weights07 leaf01263_w_segment07 := by decide +kernel
theorem leaf01263_w_piece07_identity : leaf01263_w_piece07=IntegerOuterTerms.transform 8 1 16 21 leaf01263_w_segment07 :=
  IntegerWeightedOuter.checked 8 1 16 21 leaf01263_w_segment07 leaf01263_w_piece07 leaf01263_w_weights07 leaf01263_w_weights07_identity leaf01263_w_piece07_weighted
#print axioms leaf01263_w_weights07_identity
#print axioms leaf01263_w_piece07_weighted
#print axioms leaf01263_w_piece07_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
