/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (761155/4294967296)
  b := (1674541/8589934592)
  s := [(4389307405143/4398046511104),(-13614025/34359738368),(-5369583/274877906944)]
  L := [(26971962735338341752927449/19807040628566084398385987584),(612026515693/2251799813685248),(15176484891/1125899906842624),(-96535/8796093022208),(-18745/70368744177664)]
  c := (766589287631/562949953421312)
  R := (-164974870787811/50000000000000)
  total := (-57617762601/1000000000000000)
  k := 10
  n := 32
  sFloor := (2193739448307/4398046511104)
  nFloor := (1148081674101/576460752303423488)
  eFloor := (1676944574187/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell113
