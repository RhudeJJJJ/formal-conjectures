/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell218
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1031019/262144)
  b := (141765/32768)
  s := [(3671706636669/562949953421312),(-29450062775/17592186044416),(32716373997/140737488355328)]
  L := [(10296093219133995782861/9444732965739290427392),(-170850465265/13194139533312),(7789209923/6597069766656),(-55261067/824633720832),(271189/412316860416)]
  c := (1185610710295/1099511627776)
  R := (1884797567481/50000000000000)
  total := (15868298862811/1000000000000000)
  k := 0
  n := 32
  sFloor := (178760632741/70368744177664)
  nFloor := 20605407262452877109297802117120
  eFloor := 18656628989673453542833848844288
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell218
