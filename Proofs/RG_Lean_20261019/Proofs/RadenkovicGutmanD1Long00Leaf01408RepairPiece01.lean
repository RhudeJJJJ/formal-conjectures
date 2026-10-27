/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01408RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01408_w_weights01 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 18 1 64 3 leaf01408_w_segment01)
theorem leaf01408_w_weights01_identity : leaf01408_w_weights01=IntegerWeightedOuter.weights 18 1 64 3 leaf01408_w_segment01 := by decide +kernel
noncomputable def leaf01408_w_piece01 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01408_w_weights01 leaf01408_w_segment01)
theorem leaf01408_w_piece01_weighted : leaf01408_w_piece01=IntegerWeightedOuter.applyWeights leaf01408_w_weights01 leaf01408_w_segment01 := by decide +kernel
theorem leaf01408_w_piece01_identity : leaf01408_w_piece01=IntegerOuterTerms.transform 18 1 64 3 leaf01408_w_segment01 :=
  IntegerWeightedOuter.checked 18 1 64 3 leaf01408_w_segment01 leaf01408_w_piece01 leaf01408_w_weights01 leaf01408_w_weights01_identity leaf01408_w_piece01_weighted
#print axioms leaf01408_w_weights01_identity
#print axioms leaf01408_w_piece01_weighted
#print axioms leaf01408_w_piece01_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
