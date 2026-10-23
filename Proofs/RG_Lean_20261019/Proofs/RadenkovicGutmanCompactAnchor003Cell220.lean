/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell220
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (311883/65536)
  b := (1372285/262144)
  s := [(2216503324313/562949953421312),(-1184343258955/1125899906842624),(85536227343/562949953421312)]
  L := [(161323759908390877032851/151115727451828646838272),(-47047941291/4398046511104),(2542262223/2199023255552),(-26198877/274877906944),(708777/137438953472)]
  c := (581597429875/549755813888)
  R := (2815215112929/100000000000000)
  total := (14439201248623/1000000000000000)
  k := 0
  n := 32
  sFloor := (854933961089/562949953421312)
  nFloor := 118381311290673552040035440270508032
  eFloor := 110020740386040365458513920222298112
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell220
