/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01272RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01272_w_weights22 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 66 leaf01272_w_segment22)
theorem leaf01272_w_weights22_identity : leaf01272_w_weights22=IntegerWeightedOuter.weights 8 1 16 66 leaf01272_w_segment22 := by decide +kernel
noncomputable def leaf01272_w_piece22 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01272_w_weights22 leaf01272_w_segment22)
theorem leaf01272_w_piece22_weighted : leaf01272_w_piece22=IntegerWeightedOuter.applyWeights leaf01272_w_weights22 leaf01272_w_segment22 := by decide +kernel
theorem leaf01272_w_piece22_identity : leaf01272_w_piece22=IntegerOuterTerms.transform 8 1 16 66 leaf01272_w_segment22 :=
  IntegerWeightedOuter.checked 8 1 16 66 leaf01272_w_segment22 leaf01272_w_piece22 leaf01272_w_weights22 leaf01272_w_weights22_identity leaf01272_w_piece22_weighted
#print axioms leaf01272_w_weights22_identity
#print axioms leaf01272_w_piece22_weighted
#print axioms leaf01272_w_piece22_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
