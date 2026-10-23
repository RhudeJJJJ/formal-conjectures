/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (874365/1073741824)
  b := (1923603/2147483648)
  s := [(4224040306881/4398046511104),(-16375357547/2199023255552),(-149936485/549755813888)]
  L := [(33406575804535849190977/1208925819614629174706176),(746355709503/140737488355328),(47010483535/211106232532992),(-16856395/4398046511104),(-556729/13194139533312)]
  c := (972259318355/35184372088832)
  R := (-179436736547067/100000000000000)
  total := (-17793215151/125000000000000)
  k := 6
  n := 32
  sFloor := (2095045049953/4398046511104)
  nFloor := (1515077151511/36028797018963968)
  eFloor := (1106508567987/36028797018963968)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell129
