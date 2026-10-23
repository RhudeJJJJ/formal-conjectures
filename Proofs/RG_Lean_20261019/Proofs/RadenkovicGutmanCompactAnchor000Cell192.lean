/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell192
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1384143/4194304)
  b := (1522557/4194304)
  s := [(2101175760719/8796093022208),(-65091520049/8796093022208),(-2255306501/4398046511104)]
  L := [(937348671965069706619/1180591620717411303424),(300523173631/13194139533312),(7323512051/6597069766656),(-198651307/824633720832),(7999237/412316860416)]
  c := (1745947956973/2199023255552)
  R := (-5767890926473/50000000000000)
  total := (-3566035235803/1000000000000000)
  k := 1
  n := 32
  sFloor := (507893406917/4398046511104)
  nFloor := (1222458099861/2147483648)
  eFloor := (472966153857/1073741824)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell192
