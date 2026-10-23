/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell228
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1337095/131072)
  b := (367701/32768)
  s := [(8165449262327/18014398509481984),(-2358107553297/18014398509481984),(183859730115/9007199254740992)]
  L := [(4805681736122539535827/4722366482869645213696),(-10930386305/3298534883328),(1515804923/3298534883328),(-22538429/412316860416),(997135/206158430208)]
  c := (1115716993599/1099511627776)
  R := (731556768271/100000000000000)
  total := (31873390349/3906250000000)
  k := 0
  n := 32
  sFloor := (1543765292315/9007199254740992)
  nFloor := 8193272377495072158024827510995184478648769970176
  eFloor := 8043931541561067969759813940121431999707846017024
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell228
