/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell164
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1535717/67108864)
  b := (211161/8388608)
  s := [(5765424609771/35184372088832),(-266215761321/35184372088832),(17735565633/17592186044416)]
  L := [(2305190452572420532955/2361183241434822606848),(182827309555/13194139533312),(-15240154711/6597069766656),(163273139/824633720832),(-5686613/412316860416)]
  c := (536718976817/549755813888)
  R := (-1199978400069/100000000000000)
  total := (-20217721527/1000000000000000)
  k := 1
  n := 32
  sFloor := (1383669994929/17592186044416)
  nFloor := (38115339383/1099511627776)
  eFloor := (1795056092901/70368744177664)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell164
