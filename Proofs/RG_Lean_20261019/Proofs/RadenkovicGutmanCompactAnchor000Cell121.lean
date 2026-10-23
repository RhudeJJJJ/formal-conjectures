/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (815799/2147483648)
  b := (448689/1073741824)
  s := [(4353064582487/4398046511104),(-553648835/274877906944),(-51426273/549755813888)]
  L := [(531841230936739524396897/77371252455336267181195264),(765856797349/562949953421312),(55050251149/844424930131968),(-9699193/35184372088832),(-309805/52776558133248)]
  c := (1934827126885/281474976710656)
  R := (-249001278428463/100000000000000)
  total := (-18554526687/200000000000000)
  k := 8
  n := 32
  sFloor := (2171897395471/4398046511104)
  nFloor := (1180248699719/144115188075855872)
  eFloor := (882563636587/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell121
