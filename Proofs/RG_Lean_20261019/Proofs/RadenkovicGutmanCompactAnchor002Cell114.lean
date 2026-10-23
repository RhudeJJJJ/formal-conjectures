/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell114
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1674541/8589934592)
  b := (920997/4294967296)
  s := [(4387478896615/4398046511104),(-1052934121/2199023255552),(-404359/17179869184)]
  L := [(8155542447840728267616391/4951760157141521099596496896),(2219749944433/6755399441055744),(18316275719/1125899906842624),(-6766243/422212465065984),(-27203/70368744177664)]
  c := (927177830799/562949953421312)
  R := (-160220015714709/50000000000000)
  total := (-15381430981/250000000000000)
  k := 10
  n := 32
  sFloor := (1096317378117/2199023255552)
  nFloor := (1389179581889/576460752303423488)
  eFloor := (1014552119779/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell114
