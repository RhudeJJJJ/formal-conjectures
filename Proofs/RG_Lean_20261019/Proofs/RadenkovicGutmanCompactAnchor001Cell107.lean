/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell107
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (859307/8589934592)
  b := (945237/8589934592)
  s := [(4397490574123/4398046511104),(-55582125/2199023255552),(-694121/549755813888)]
  L := [(167760866355324307338308723/2535301200456458802993406410752),(715102461299/54043195528445952),(35734974829/54043195528445952),(-124061/3377699720527872),(-3097/3377699720527872)]
  c := (1192012649335/18014398509481984)
  R := (-120291043173293/25000000000000)
  total := (-9529885683/200000000000000)
  k := 14
  n := 32
  sFloor := (549671732113/1099511627776)
  nFloor := (1108601799203/2305843009213693952)
  eFloor := (1058955427587/2305843009213693952)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell107
