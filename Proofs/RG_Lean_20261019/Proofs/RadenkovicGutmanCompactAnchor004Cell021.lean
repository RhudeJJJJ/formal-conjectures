/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (242489/8796093022208)
  b := (1066951/35184372088832)
  s := [(1099511627727/1099511627776),(-39/4398046511104),(-1/2199023255552)]
  L := [(4676232281781/151115727451828646838272),(2805722013053/453347182355485940514816),(23380872155/75557863725914323419136),(-11/28334198897217871282176),(1/4722366482869645213696)]
  c := (1169058070445/37778931862957161709568)
  R := (-241988190694947/20000000000000)
  total := (-3322177/100000000000000)
  k := 35
  n := 32
  sFloor := (2199023255433/4398046511104)
  nFloor := (514783209353/9671406556917033397649408)
  eFloor := (184462470529/4835703278458516698824704)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell021
