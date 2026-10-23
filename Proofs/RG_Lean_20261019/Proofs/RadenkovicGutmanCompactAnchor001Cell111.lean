/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell111
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1258109/8589934592)
  b := (1383919/8589934592)
  s := [(4396855090705/4398046511104),(-119090115/2199023255552),(-2971265/1099511627776)]
  L := [(89887967031742536159947167/633825300114114700748351602688),(191549341213/6755399441055744),(12754666497/9007199254740992),(-17797/105553116266496),(-2365/562949953421312)]
  c := (319346210033/2251799813685248)
  R := (-27690514248209/6250000000000)
  total := (-64181042889/1000000000000000)
  k := 13
  n := 32
  sFloor := (2198302512707/4398046511104)
  nFloor := (594095003327/576460752303423488)
  eFloor := (567489667587/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell111
