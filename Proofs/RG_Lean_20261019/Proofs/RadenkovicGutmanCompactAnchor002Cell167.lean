/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell167
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (511009/16777216)
  b := (1124219/33554432)
  s := [(5216388931851/35184372088832),(-116967208597/35184372088832),(13414337305/17592186044416)]
  L := [(1183566473426953523909/1180591620717411303424),(58621722361/13194139533312),(-12478568411/6597069766656),(144125981/824633720832),(-5108377/412316860416)]
  c := (275570543815/274877906944)
  R := (125831444453/100000000000000)
  total := (3154795693/500000000000000)
  k := 0
  n := 32
  sFloor := (640781299733/8796093022208)
  nFloor := (558208300271/8796093022208)
  eFloor := (1652080828983/35184372088832)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell167
