/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01336RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01336_w_weights02 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 32 6 leaf01336_w_segment02)
theorem leaf01336_w_weights02_identity : leaf01336_w_weights02=IntegerWeightedOuter.weights 12 1 32 6 leaf01336_w_segment02 := by decide +kernel
noncomputable def leaf01336_w_piece02 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01336_w_weights02 leaf01336_w_segment02)
theorem leaf01336_w_piece02_weighted : leaf01336_w_piece02=IntegerWeightedOuter.applyWeights leaf01336_w_weights02 leaf01336_w_segment02 := by decide +kernel
theorem leaf01336_w_piece02_identity : leaf01336_w_piece02=IntegerOuterTerms.transform 12 1 32 6 leaf01336_w_segment02 :=
  IntegerWeightedOuter.checked 12 1 32 6 leaf01336_w_segment02 leaf01336_w_piece02 leaf01336_w_weights02 leaf01336_w_weights02_identity leaf01336_w_piece02_weighted
#print axioms leaf01336_w_weights02_identity
#print axioms leaf01336_w_piece02_weighted
#print axioms leaf01336_w_piece02_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
