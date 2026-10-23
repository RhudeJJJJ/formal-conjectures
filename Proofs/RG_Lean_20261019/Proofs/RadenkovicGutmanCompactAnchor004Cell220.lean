/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell220
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (311883/65536)
  b := (1372285/262144)
  s := [(2216503324313/562949953421312),(-1184343258955/1125899906842624),(85536227343/562949953421312)]
  L := [(161323759908550573653671/151115727451828646838272),(-141143823889/13194139533312),(7626786725/6597069766656),(-78596645/824633720832),(2126335/412316860416)]
  c := (145399357469/137438953472)
  R := (563043022603/20000000000000)
  total := (7219600624421/500000000000000)
  k := 0
  n := 32
  sFloor := (854933961089/562949953421312)
  nFloor := 2913161804818680760565176869874302976
  eFloor := 2707422439708633382806193957941280768
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell220
