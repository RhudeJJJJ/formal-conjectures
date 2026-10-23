/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell215
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (193655/65536)
  b := (426041/131072)
  s := [(3741453286009/281474976710656),(-883049593387/281474976710656),(56469012487/140737488355328)]
  L := [(2669215982553072773223/2361183241434822606848),(-194615812685/13194139533312),(4911335443/6597069766656),(33235547/824633720832),(-4559479/412316860416)]
  c := (613791638753/549755813888)
  R := (1101813150981/20000000000000)
  total := (8591346124067/500000000000000)
  k := 0
  n := 32
  sFloor := (742835429399/140737488355328)
  nFloor := 8444942434012779943821312
  eFloor := 7274387485142060766330880
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell215
