/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell244
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (47999/1024)
  b := (422391/8192)
  s := [(2793429802173/576460752303423488),(-1651528020101/1152921504606846976),(131757261031/576460752303423488)]
  L := [(18906448439301872294609/18889465931478580854784),(-1177804013/6597069766656),(21889357/824633720832),(-706061/206158430208),(33715/103079215104)]
  c := (1100329618941/1099511627776)
  R := (3718410153/10000000000000)
  total := (957984436771/500000000000000)
  k := 0
  n := 32
  sFloor := (2099423053153/1152921504606846976)
  nFloor := 67722010102017262428379107317355139168191710299593469594769785598332895232
  eFloor := 67660523801136524355607445753131616599265501700981034582490372205765984256
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell244
