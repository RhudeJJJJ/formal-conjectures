/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1153433/281474976710656)
  b := (158597/35184372088832)
  s := [(4398046511103/4398046511104),(-3/4398046511104),(1/2199023255552)]
  L := [(2188382301219/19342813113834066795298816),(1313025965615/58028439341502200385896448),(8206390951/7253554917687775048237056),(-1/453347182355485940514816),(1/906694364710971881029632)]
  c := (2188382301219/19342813113834066795298816)
  R := (-298101794554759/20000000000000)
  total := (-3043991/500000000000000)
  k := 44
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1083545966087/1237940039285380274899124224)
  eFloor := (1036499543779/1237940039285380274899124224)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell001
