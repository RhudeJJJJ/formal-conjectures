/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell187
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (859445/4194304)
  b := (1890779/8388608)
  s := [(329978916787/1099511627776),(-64195537711/8796093022208),(-1091155629/4398046511104)]
  L := [(768727929406389842809/1180591620717411303424),(42684542417/2199023255552),(2802892547/6597069766656),(-11990531/137438953472),(2869285/412316860416)]
  c := (1431867348787/2199023255552)
  R := (-21451692815507/100000000000000)
  total := (-2121268112857/500000000000000)
  k := 1
  n := 32
  sFloor := (1286726742663/8796093022208)
  nFloor := (115021652305/4294967296)
  eFloor := (760750808117/34359738368)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell187
