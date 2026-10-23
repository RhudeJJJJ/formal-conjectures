/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (851807/1099511627776)
  b := (936987/1099511627776)
  s := [(4398046321083/4398046511104),(-9501/1099511627776),(-475/1099511627776)]
  L := [(2131667573979/73786976294838206464),(159873747185/27670116110564327424),(31974481045/110680464442257309696),(-35/6917529027641081856),(-1/6917529027641081856)]
  c := (2131667573979/73786976294838206464)
  R := (-867989411451503/100000000000000)
  total := (-83585993/125000000000000)
  k := 26
  n := 32
  sFloor := (2199023140589/4398046511104)
  nFloor := (1286723320263/37778931862957161709568)
  eFloor := (962181421053/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell056
