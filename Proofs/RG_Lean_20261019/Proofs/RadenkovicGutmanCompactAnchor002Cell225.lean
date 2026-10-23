/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell225
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (2009161/262144)
  b := (552519/65536)
  s := [(584775224857/562949953421312),(-1326940922367/4503599627370496),(101646377025/2251799813685248)]
  L := [(2431798693405951240009/2361183241434822606848),(-71328327977/13194139533312),(4696790285/6597069766656),(-65399377/824633720832),(2703487/412316860416)]
  c := (1127153291223/1099511627776)
  R := (155182102473/12500000000000)
  total := (10366891571743/1000000000000000)
  k := 0
  n := 32
  sFloor := (1777276815269/4503599627370496)
  nFloor := 12619848890225919375162812033957386881335296
  eFloor := 12227958640249102957407428168170576860413952
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell225
