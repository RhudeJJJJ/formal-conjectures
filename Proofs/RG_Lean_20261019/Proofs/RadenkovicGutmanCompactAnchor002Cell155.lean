/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell155
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1302593/134217728)
  b := (358213/33554432)
  s := [(5173255751309/17592186044416),(-414450612729/17592186044416),(17542146029/8796093022208)]
  L := [(3522443882001273828635/4722366482869645213696),(506694881165/13194139533312),(-19778417899/6597069766656),(155556661/824633720832),(-3873809/412316860416)]
  c := (1640265752561/2199023255552)
  R := (-7328875351909/50000000000000)
  total := (-65285004863/500000000000000)
  k := 1
  n := 32
  sFloor := (1198472357659/8796093022208)
  nFloor := (1694281552897/281474976710656)
  eFloor := (619554188475/140737488355328)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell155
