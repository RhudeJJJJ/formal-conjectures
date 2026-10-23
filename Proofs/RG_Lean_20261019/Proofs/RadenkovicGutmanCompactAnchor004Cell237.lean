/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell237
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1576395/65536)
  b := (867017/32768)
  s := [(2570664141603/72057594037927936),(-378695500601/36028797018963968),(60226774305/36028797018963968)]
  L := [(37905996398007913802845/37778931862957161709568),(-4362211553/6597069766656),(160246133/1649267441664),(-5102449/412316860416),(120433/103079215104)]
  c := (1102577166045/1099511627776)
  R := (139210564891/100000000000000)
  total := (3677329947569/1000000000000000)
  k := 0
  n := 32
  sFloor := (1933726689011/144115188075855872)
  nFloor := 1450608904189874797224855208372385313109205417527793156004916242006671360
  eFloor := 1445643172598320518380999858777011809702364264738155191888864715948949504
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell237
