/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell082
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1268985/137438953472)
  b := (1395883/137438953472)
  s := [(549753078711/549755813888),(-547029/549755813888),(-54701/1099511627776)]
  L := [(1126451685762398765750557267/324518553658426726783156020576256),(400192416109/576460752303423488),(2501141787/72057594037927936),(-2547/36028797018963968),(-1/562949953421312)]
  c := (2000980156257/576460752303423488)
  R := (-628551269923443/100000000000000)
  total := (-230349947/40000000000000)
  k := 19
  n := 32
  sFloor := (1099505008663/2199023255552)
  nFloor := (440558201323/73786976294838206464)
  eFloor := (1262923154957/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell082
