/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell157
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1576137/134217728)
  b := (866875/67108864)
  s := [(2224107241539/8796093022208),(-343904757677/17592186044416),(15521506779/8796093022208)]
  L := [(7696505954017810997117/9444732965739290427392),(74424212401/2199023255552),(-616559477/206158430208),(3601853/17179869184),(-1238927/103079215104)]
  c := (1791982435159/2199023255552)
  R := (-639658669791/6250000000000)
  total := (-54410030703/500000000000000)
  k := 1
  n := 32
  sFloor := (2067676369479/17592186044416)
  nFloor := (1244769273013/140737488355328)
  eFloor := (227736199455/35184372088832)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell157
