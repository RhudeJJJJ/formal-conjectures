/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell176
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1204927/16777216)
  b := (1325419/16777216)
  s := [(2632219610241/8796093022208),(76192908543/17592186044416),(-1335221489/8796093022208)]
  L := [(2765061569957899926279/4722366482869645213696),(-17749278849/8796093022208),(1970098805/13194139533312),(39043029/549755813888),(-7308677/824633720832)]
  c := (1283609842551/2199023255552)
  R := (-13458424721953/50000000000000)
  total := (-1927831615997/1000000000000000)
  k := 1
  n := 32
  sFloor := (20564215705/137438953472)
  nFloor := (853888306527/2199023255552)
  eFloor := (786552188739/2199023255552)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell176
