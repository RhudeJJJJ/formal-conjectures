/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell152
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (978659/134217728)
  b := (269131/33554432)
  s := [(6516906459365/17592186044416),(-521708643003/17592186044416),(19858908363/8796093022208)]
  L := [(23744532271805626730397/37778931862957161709568),(285194190019/6597069766656),(-18051296249/6597069766656),(54000077/412316860416),(-1590991/412316860416)]
  c := (691056841513/1099511627776)
  R := (-23219965263981/100000000000000)
  total := (-157534653199/1000000000000000)
  k := 1
  n := 32
  sFloor := (94295556767/549755813888)
  nFloor := (476576805531/140737488355328)
  eFloor := (696663068009/281474976710656)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell152
