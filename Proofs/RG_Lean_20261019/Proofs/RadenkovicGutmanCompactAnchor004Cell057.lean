/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (936987/1099511627776)
  b := (1030685/1099511627776)
  s := [(4398046324701/4398046511104),(-37283/4398046511104),(-931/2199023255552)]
  L := [(4363742545747/147573952589676412928),(163639115849/27670116110564327424),(8181893243/27670116110564327424),(-67/13835058055282163712),(-1/3458764513820540928)]
  c := (2181871272873/73786976294838206464)
  R := (-86682549551871/10000000000000)
  total := (-91820609/125000000000000)
  k := 26
  n := 32
  sFloor := (1099511571389/2199023255552)
  nFloor := (960765571361/18889465931478580854784)
  eFloor := (688543012573/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell057
