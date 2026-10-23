/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell162
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1269189/67108864)
  b := (1396107/67108864)
  s := [(6378444056547/35184372088832),(-187310680611/17592186044416),(10555032303/8796093022208)]
  L := [(4458136844910169732601/4722366482869645213696),(263053152457/13194139533312),(-5640113997/2199023255552),(43399865/206158430208),(-1955837/137438953472)]
  c := (1037990871097/1099511627776)
  R := (-44983684741/1562500000000)
  total := (-45326587399/1000000000000000)
  k := 1
  n := 32
  sFloor := (755755353067/8796093022208)
  nFloor := (1643682580959/70368744177664)
  eFloor := (1206705101201/70368744177664)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell162
