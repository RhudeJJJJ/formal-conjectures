/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1163779/1073741824)
  b := (320039/268435456)
  s := [(4103235141515/4398046511104),(-26560941753/2199023255552),(-185631603/549755813888)]
  L := [(28701601125029064405469/604462909807314587353088),(1867375527707/211106232532992),(11365400543/35184372088832),(-131494247/13194139533312),(-39703/2199023255552)]
  c := (1670653065959/35184372088832)
  R := (-30473874018229/20000000000000)
  total := (-80139664789/500000000000000)
  k := 5
  n := 32
  sFloor := (31629907853/68719476736)
  nFloor := (671040294247/9007199254740992)
  eFloor := (980171230003/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell132
