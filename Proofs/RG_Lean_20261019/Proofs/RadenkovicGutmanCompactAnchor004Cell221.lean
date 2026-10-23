/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell221
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1372285/262144)
  b := (1509513/262144)
  s := [(3419735844357/1125899906842624),(-1856821819483/2251799813685248),(136237300455/1125899906842624)]
  L := [(9991767755642159203653/9444732965739290427392),(-125550515365/13194139533312),(2396879153/2199023255552),(-81797465/824633720832),(871963/137438953472)]
  c := (1153828667939/1099511627776)
  R := (482195826037/20000000000000)
  total := (6820555008423/500000000000000)
  k := 0
  n := 32
  sFloor := (1313781117535/1125899906842624)
  nFloor := 290608753433197388325102982730921017344
  eFloor := 273034696453311283196763808735931924480
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell221
