/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (679931/70368744177664)
  b := (186981/17592186044416)
  s := [(2199023255537/2199023255552),(-3/2199023255552)]
  L := [(1529207983103848163699217947/340282366920938463463374607431768211456),(3259698077407/3626777458843887524118528),(27164110677/604462909807314587353088),(11/226673591177742970257408),(-1/37778931862957161709568)]
  c := (1358209529825/302231454903657293676544)
  R := (-326603645719543/25000000000000)
  total := (-12576311/1000000000000000)
  k := 38
  n := 32
  sFloor := (1099511627767/2199023255552)
  nFloor := (1639692623907/309485009821345068724781056)
  eFloor := (1226123560601/309485009821345068724781056)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell010
