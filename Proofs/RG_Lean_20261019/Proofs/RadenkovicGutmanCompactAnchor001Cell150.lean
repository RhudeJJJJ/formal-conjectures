/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell150
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1617619/268435456)
  b := (444845/67108864)
  s := [(3209902106237/4398046511104),(-286874513083/8796093022208),(3958653573/4398046511104)]
  L := [(3089258584183057723959/18889465931478580854784),(803089874245/35184372088832),(-8445096769/52776558133248),(-98026601/2199023255552),(10330825/3298534883328)]
  c := (1438548129137/8796093022208)
  R := (-4526683217089/5000000000000)
  total := (-105111629673/200000000000000)
  k := 3
  n := 32
  sFloor := (767605875817/2199023255552)
  nFloor := (246382914821/140737488355328)
  eFloor := (941104071525/562949953421312)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell150
