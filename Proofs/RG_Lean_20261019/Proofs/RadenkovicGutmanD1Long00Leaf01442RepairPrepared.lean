/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01442_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 56923460860903424000000000000 62392945403737700805332199827 9194626486894364501187500000000))
theorem leaf01442_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 56923460860903424000000000000 62392945403737700805332199827 9194626486894364501187500000000 leaf01442_w_raw=true := by decide +kernel
theorem leaf01442_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01442_w_raw=true := by decide +kernel
#print axioms leaf01442_raw
#print axioms leaf01442_rectangular
noncomputable def leaf01442_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01442_w_raw ![16,254,127] ![1,1,1] ![64,256,128])
theorem leaf01442_inner : leaf01442_w_inner=IntegerAffineStages.inner leaf01442_w_raw ![16,254,127] ![1,1,1] ![64,256,128] := by decide +kernel
#print axioms leaf01442_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
