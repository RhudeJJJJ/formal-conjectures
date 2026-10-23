/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (64985/536870912)
  b := (142967/1073741824)
  s := [(2197145337543/2199023255552),(-375100167/2199023255552),(-9321095/1099511627776)]
  L := [(94449160611647516972490969/158456325028528675187087900672),(1609235856365/13510798882111488),(13363412889/2251799813685248),(-109655/52776558133248),(-7219/140737488355328)]
  c := (41943853107/70368744177664)
  R := (-371258628783443/100000000000000)
  total := (-44353245389/1000000000000000)
  k := 11
  n := 32
  sFloor := (1098375797593/2199023255552)
  nFloor := (591544096313/576460752303423488)
  eFloor := (1695746307173/2305843009213693952)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell109
