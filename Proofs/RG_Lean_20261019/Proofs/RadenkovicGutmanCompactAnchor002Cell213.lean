/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell213
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (320091/131072)
  b := (88025/32768)
  s := [(5794154116673/281474976710656),(-158761037727/35184372088832),(37778596287/70368744177664)]
  L := [(85435564025269829569/73786976294838206464),(-89679563713/6597069766656),(28030421/824633720832),(7488005/51539607552),(-1996231/103079215104)]
  c := (629159171073/549755813888)
  R := (3372751849157/50000000000000)
  total := (17183182906423/1000000000000000)
  k := 0
  n := 32
  sFloor := (1168795050001/140737488355328)
  nFloor := 5339694736072759050240
  eFloor := 4425629417998108327936
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell213
