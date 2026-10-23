/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell235
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1302807/65536)
  b := (1433087/65536)
  s := [(2269673601727/36028797018963968),(-1334637437731/72057594037927936),(105911531537/36028797018963968)]
  L := [(37963590660932474261651/37778931862957161709568),(-6305640601/6597069766656),(460282247/3298534883328),(-7274495/412316860416),(341125/206158430208)]
  c := (137996351765/137438953472)
  R := (101185113767/50000000000000)
  total := (137988895503/31250000000000)
  k := 0
  n := 32
  sFloor := (854133207199/36028797018963968)
  nFloor := 74939404172579456577351405691700711409696425030452259166156696322048
  eFloor := 74565495910801693398860428732799225176051664845114882964589985660928
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell235
