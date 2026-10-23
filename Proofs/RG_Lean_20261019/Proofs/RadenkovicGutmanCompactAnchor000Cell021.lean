/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (242489/8796093022208)
  b := (1066951/35184372088832)
  s := [(4398046510863/4398046511104),(-49/4398046511104),(-1/2199023255552)]
  L := [(1556004841232064626674815485/42535295865117307932921825928971026432),(1105601097565/151115727451828646838272),(82919569367/226673591177742970257408),(-1/9444732965739290427392),(1/14167099448608935641088)]
  c := (1382009920931/37778931862957161709568)
  R := (-240314785220711/20000000000000)
  total := (-32991111/1000000000000000)
  k := 35
  n := 32
  sFloor := (1099511627703/2199023255552)
  nFloor := (417106385993/9671406556917033397649408)
  eFloor := (1247609362113/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell021
