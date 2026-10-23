/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell244
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (47999/1024)
  b := (422391/8192)
  s := [(2793429802173/576460752303423488),(-1651528020101/1152921504606846976),(131757261031/576460752303423488)]
  L := [(151251587514511300257385/151115727451828646838272),(-1177804013/6597069766656),(21889357/824633720832),(-706061/206158430208),(33715/103079215104)]
  c := (550164809471/549755813888)
  R := (4648012697/12500000000000)
  total := (95798443753/50000000000000)
  k := 0
  n := 32
  sFloor := (2099423053153/1152921504606846976)
  nFloor := 148932558006708342321296029271504051170747378982536960024118922804703025692672
  eFloor := 148797338865275397843292640376961178301576415478966712757667950457411310977024
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell244
