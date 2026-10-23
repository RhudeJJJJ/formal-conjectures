/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell237
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1576395/65536)
  b := (867017/32768)
  s := [(2570664141603/72057594037927936),(-378695500601/36028797018963968),(60226774305/36028797018963968)]
  L := [(37905996397898652316867/37778931862957161709568),(-4362211553/6597069766656),(160246133/1649267441664),(-5102449/412316860416),(120433/103079215104)]
  c := (551288583021/549755813888)
  R := (27842112951/20000000000000)
  total := (1838664972051/500000000000000)
  k := 0
  n := 32
  sFloor := (1933726689011/144115188075855872)
  nFloor := 4303412576086763767895742031939267304591791634453438958496999538688
  eFloor := 4288681112822263458317150724780008576985768029381595053330721144832
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell237
