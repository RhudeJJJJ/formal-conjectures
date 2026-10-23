/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell240
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1049089/32768)
  b := (1153997/32768)
  s := [(2187099003241/144115188075855872),(-1291288857927/288230376151711744),(51439775735/72057594037927936)]
  L := [(9462808906649577052321/9444732965739290427392),(-2496004645/6597069766656),(7691239/137438953472),(-740075/103079215104),(23443/34359738368)]
  c := (550627164717/549755813888)
  R := (79186158643/100000000000000)
  total := (1392801315231/500000000000000)
  k := 0
  n := 32
  sFloor := (1644334125747/288230376151711744)
  nFloor := 3593929747660213354407381206169023913342884521723227544043187601408
  eFloor := 3586955717040925125051475487102082521690777721120863876709500321792
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell240
