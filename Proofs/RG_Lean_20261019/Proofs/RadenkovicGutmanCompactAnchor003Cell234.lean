/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell234
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (592185/32768)
  b := (1302807/65536)
  s := [(3014479189507/36028797018963968),(-442545662835/18014398509481984),(70142868945/18014398509481984)]
  L := [(19000678260435924899403/18889465931478580854784),(-15139590341/13194139533312),(1100570267/6597069766656),(-17311999/824633720832),(808309/412316860416)]
  c := (17263842281/17179869184)
  R := (121899266659/50000000000000)
  total := (4834437692849/1000000000000000)
  k := 0
  n := 32
  sFloor := (1134836800863/36028797018963968)
  nFloor := 1650104894467821491497797222517503461887254673521920052197064704
  eFloor := 1640172226308982978832312219678366436005151054911853518401830912
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell234
