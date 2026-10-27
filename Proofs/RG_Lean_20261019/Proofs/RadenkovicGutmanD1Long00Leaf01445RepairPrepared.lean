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
noncomputable def leaf01445_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 386890647447011328000000000000 420464280939025744424048034357 72932443398646549853500000000000))
theorem leaf01445_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 386890647447011328000000000000 420464280939025744424048034357 72932443398646549853500000000000 leaf01445_w_raw=true := by decide +kernel
theorem leaf01445_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01445_w_raw=true := by decide +kernel
#print axioms leaf01445_raw
#print axioms leaf01445_rectangular
noncomputable def leaf01445_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01445_w_raw ![15,0,0] ![1,1,1] ![64,2,1])
theorem leaf01445_inner : leaf01445_w_inner=IntegerAffineStages.inner leaf01445_w_raw ![15,0,0] ![1,1,1] ![64,2,1] := by decide +kernel
#print axioms leaf01445_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
