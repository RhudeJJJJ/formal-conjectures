/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell253
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (452715/4096)
  b := (995973/8192)
  s := [(853610927279/2305843009213693952),(-252584081857/2305843009213693952),(80681653307/4611686018427387904)]
  L := [(604561394852775903270739/604462909807314587353088),(-142942963/4398046511104),(10679559/2199023255552),(-173145/274877906944),(8305/137438953472)]
  c := (17182183577/17179869184)
  R := (3367658241/50000000000000)
  total := (818675531791/1000000000000000)
  k := 0
  n := 32
  sFloor := (1282735344151/9223372036854775808)
  nFloor := 36563999228575617788177458651796738541432703204251178714396699985561373276788415814515233542879978264199168
  eFloor := 36558015764319929887191124042963582914019957737956718664595293065390428271826052969939063848130302311399424
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell253
