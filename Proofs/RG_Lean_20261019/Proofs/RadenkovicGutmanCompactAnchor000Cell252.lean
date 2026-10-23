/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell252
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (823119/8192)
  b := (452715/4096)
  s := [(4544292551099/9223372036854775808),(-1344584307485/9223372036854775808),(107367732751/4611686018427387904)]
  L := [(604582014810703661035681/604462909807314587353088),(-518456143/13194139533312),(12907395/2199023255552),(-627557/824633720832),(10029/137438953472)]
  c := (1099690771023/1099511627776)
  R := (8145828119/100000000000000)
  total := (112509616201/125000000000000)
  k := 0
  n := 32
  sFloor := (853610927279/4611686018427387904)
  nFloor := 24780982041481191242727707029425595881049271558439923612081024827308474203370863781216256
  eFloor := 24776075676988686658877155202602642366610494379638421515130607340032356758732330934206464
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell252
