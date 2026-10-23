/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (542913/1073741824)
  b := (149301/268435456)
  s := [(1095978487433/1099511627776),(-2812135001/4398046511104),(-68636695/2199023255552)]
  L := [(1042792335208455818071487/618970019642690137449562112),(283518258883/844424930131968),(27951622837/1688849860263936),(-4958749/211106232532992),(-58939/105553116266496)]
  c := (1896828207843/1125899906842624)
  R := (-39913467407067/12500000000000)
  total := (-39752863229/250000000000000)
  k := 10
  n := 32
  sFloor := (1095241135335/2199023255552)
  nFloor := (442536924489/36028797018963968)
  eFloor := (845435919297/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell124
