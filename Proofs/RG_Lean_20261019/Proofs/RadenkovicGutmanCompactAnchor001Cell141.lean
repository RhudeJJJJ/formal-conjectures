/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell141
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (343015/134217728)
  b := (754633/268435456)
  s := [(8153997352023/8796093022208),(-113861843545/8796093022208),(-1417439409/4398046511104)]
  L := [(23972844394819349243413/604462909807314587353088),(1539712522909/211106232532992),(26303080181/105553116266496),(-123830041/13194139533312),(83371/6597069766656)]
  c := (43606349927/1099511627776)
  R := (-161370930258673/100000000000000)
  total := (-100273130523/250000000000000)
  k := 5
  n := 32
  sFloor := (2009325157415/4398046511104)
  nFloor := (707024657829/2251799813685248)
  eFloor := (337662147789/1125899906842624)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell141
