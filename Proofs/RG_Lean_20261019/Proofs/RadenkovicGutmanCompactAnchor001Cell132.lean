/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1163779/1073741824)
  b := (320039/268435456)
  s := [(2167141380615/2199023255552),(-12461122739/4398046511104),(-278594363/2199023255552)]
  L := [(147865078822651729023627/19342813113834066795298816),(846965474823/562949953421312),(59486095133/844424930131968),(-16182787/35184372088832),(-473717/52776558133248)]
  c := (2151720092263/281474976710656)
  R := (-243688799287999/100000000000000)
  total := (-10358542011/40000000000000)
  k := 8
  n := 32
  sFloor := (1080316112441/2199023255552)
  nFloor := (508402939459/9007199254740992)
  eFloor := (971260688741/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell132
