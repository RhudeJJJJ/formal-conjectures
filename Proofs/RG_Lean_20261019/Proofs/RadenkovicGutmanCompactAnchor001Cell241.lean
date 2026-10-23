/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell241
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1153997/32768)
  b := (317349/8192)
  s := [(3288668251495/288230376151711744),(-971266483897/288230376151711744),(77416581089/144115188075855872)]
  L := [(18919405318967754933395/18889465931478580854784),(-4139842343/13194139533312),(306648763/6597069766656),(-4926397/824633720832),(234437/412316860416)]
  c := (8601207089/8589934592)
  R := (32785776607/50000000000000)
  total := (317210001123/125000000000000)
  k := 0
  n := 32
  sFloor := (154514683111/36028797018963968)
  nFloor := 293642882455980489618706945173511237709344179280977342330302713722568704
  eFloor := 293171511221293725958000727839246840129857406066169048539539267599204352
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell241
