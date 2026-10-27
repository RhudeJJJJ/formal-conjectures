/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01347RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01347_w_weights01 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 11 1 32 3 leaf01347_w_segment01)
theorem leaf01347_w_weights01_identity : leaf01347_w_weights01=IntegerWeightedOuter.weights 11 1 32 3 leaf01347_w_segment01 := by decide +kernel
noncomputable def leaf01347_w_piece01 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01347_w_weights01 leaf01347_w_segment01)
theorem leaf01347_w_piece01_weighted : leaf01347_w_piece01=IntegerWeightedOuter.applyWeights leaf01347_w_weights01 leaf01347_w_segment01 := by decide +kernel
theorem leaf01347_w_piece01_identity : leaf01347_w_piece01=IntegerOuterTerms.transform 11 1 32 3 leaf01347_w_segment01 :=
  IntegerWeightedOuter.checked 11 1 32 3 leaf01347_w_segment01 leaf01347_w_piece01 leaf01347_w_weights01 leaf01347_w_weights01_identity leaf01347_w_piece01_weighted
#print axioms leaf01347_w_weights01_identity
#print axioms leaf01347_w_piece01_weighted
#print axioms leaf01347_w_piece01_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
