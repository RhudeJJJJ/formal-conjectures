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
noncomputable def leaf01409_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 78027629589031813120000000000 86986309661490887990387483301 9576181082613558374100000000000))
theorem leaf01409_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 78027629589031813120000000000 86986309661490887990387483301 9576181082613558374100000000000 leaf01409_w_raw=true := by decide +kernel
theorem leaf01409_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01409_w_raw=true := by decide +kernel
#print axioms leaf01409_raw
#print axioms leaf01409_rectangular
noncomputable def leaf01409_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01409_w_raw ![18,255,254] ![1,1,1] ![64,256,256])
theorem leaf01409_inner : leaf01409_w_inner=IntegerAffineStages.inner leaf01409_w_raw ![18,255,254] ![1,1,1] ![64,256,256] := by decide +kernel
#print axioms leaf01409_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
