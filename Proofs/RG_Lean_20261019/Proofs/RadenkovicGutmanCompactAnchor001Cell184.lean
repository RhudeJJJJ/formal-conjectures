/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell184
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1291429/8388608)
  b := (1420571/8388608)
  s := [(2768232645965/8796093022208),(-50345190345/17592186044416),(-5054252065/8796093022208)]
  L := [(22940681833860710973683/37778931862957161709568),(297823854829/26388279066624),(11103812939/13194139533312),(-146302429/1649267441664),(3864877/824633720832)]
  c := (1335323429309/2199023255552)
  R := (-12470993884353/50000000000000)
  total := (-3765465557581/1000000000000000)
  k := 1
  n := 32
  sFloor := (1369002899363/8796093022208)
  nFloor := (831556599321/137438953472)
  eFloor := (713802456269/137438953472)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell184
