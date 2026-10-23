/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell160
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (524459/33554432)
  b := (1153809/67108864)
  s := [(450455224483/2199023255552),(-246146158091/17592186044416),(12441208855/8796093022208)]
  L := [(4252118206033688715149/4722366482869645213696),(340266559801/13194139533312),(-2296098977/824633720832),(179177051/824633720832),(-22577/1610612736)]
  c := (990023418803/1099511627776)
  R := (-52446393623/1000000000000)
  total := (-71632913619/1000000000000000)
  k := 1
  n := 32
  sFloor := (1691189027741/17592186044416)
  nFloor := (1112273530591/70368744177664)
  eFloor := (815244911391/70368744177664)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell160
