/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (920997/4294967296)
  b := (126637/536870912)
  s := [(4395493869435/4398046511104),(-255027805/2199023255552),(-6348279/1099511627776)]
  L := [(192616592266806964305368549/633825300114114700748351602688),(1641288316607/27021597764222976),(13642424315/4503599627370496),(-1305821/1688849860263936),(-5391/281474976710656)]
  c := (342155801055/1125899906842624)
  R := (-202470674977081/50000000000000)
  total := (-85796190213/1000000000000000)
  k := 12
  n := 32
  sFloor := (1098739605177/2199023255552)
  nFloor := (318373422685/144115188075855872)
  eFloor := (1216462611383/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell115
