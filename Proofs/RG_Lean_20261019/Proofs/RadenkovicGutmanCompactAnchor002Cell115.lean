/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (920997/4294967296)
  b := (126637/536870912)
  s := [(4385269512469/4398046511104),(-636053037/1099511627776),(-15576939/549755813888)]
  L := [(2465777731803595755722183/1237940039285380274899124224),(223593888327/562949953421312),(11046983263/562949953421312),(-411461/17592186044416),(-19699/35184372088832)]
  c := (280326472853/140737488355328)
  R := (-62186967509471/20000000000000)
  total := (-65640511707/1000000000000000)
  k := 9
  n := 32
  sFloor := (547825085601/1099511627776)
  nFloor := (840453196833/288230376151711744)
  eFloor := (153450944237/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell115
