/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell243
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1396335/32768)
  b := (47999/1024)
  s := [(7433211587679/1152921504606846976),(-2196779942059/1152921504606846976),(175213979363/576460752303423488)]
  L := [(37819970763485020992879/37778931862957161709568),(-947880483/4398046511104),(211177685/6597069766656),(-1134031/274877906944),(162295/412316860416)]
  c := (1100500139801/1099511627776)
  R := (44932127459/100000000000000)
  total := (526136441753/250000000000000)
  k := 0
  n := 32
  sFloor := (698357450543/288230376151711744)
  nFloor := 6165274844597423689408535634793551774990668290802727720198062869917423113833807872
  eFloor := 6158505418614414750471520343519883395017515879921185091959980560269992788622311424
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell243
