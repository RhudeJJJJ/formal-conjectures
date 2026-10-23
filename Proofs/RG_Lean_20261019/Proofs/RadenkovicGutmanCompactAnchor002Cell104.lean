/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell104
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (645611/8589934592)
  b := (177543/2147483648)
  s := [(1099117696645/1099511627776),(-39371805/549755813888),(-3927247/1099511627776)]
  L := [(276218211507/1125899906842624),(220893348293/4503599627370496),(16542722935/6755399441055744),(-201925/562949953421312),(-1883/211106232532992)]
  c := (276218211507/1125899906842624)
  R := (-2078225504077/500000000000)
  total := (-7718938357/250000000000000)
  k := 12
  n := 32
  sFloor := (274758756447/549755813888)
  nFloor := (825976126455/2305843009213693952)
  eFloor := (1206460900095/4611686018427387904)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell104
