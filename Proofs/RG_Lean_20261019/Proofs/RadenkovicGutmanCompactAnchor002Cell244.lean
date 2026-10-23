/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell244
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (47999/1024)
  b := (422391/8192)
  s := [(2793429802173/576460752303423488),(-3303056040203/2305843009213693952),(263514522063/1152921504606846976)]
  L := [(9453224219659192278789/9444732965739290427392),(-1177804013/6597069766656),(21889357/824633720832),(-706061/206158430208),(33715/103079215104)]
  c := (550164809471/549755813888)
  R := (4648012697/12500000000000)
  total := (383193775123/200000000000000)
  k := 0
  n := 32
  sFloor := (2099423053153/1152921504606846976)
  nFloor := 327528772418877208374304371657557420335220340917420521013021755389742262058483712
  eFloor := 327231401850407838961728866190535802961982088247775281657748498560540216033017856
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell244
