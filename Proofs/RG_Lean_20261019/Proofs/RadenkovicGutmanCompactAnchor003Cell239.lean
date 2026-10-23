/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell239
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (476859/16384)
  b := (1049089/32768)
  s := [(5817205770727/288230376151711744),(-1716354747147/288230376151711744),(136673491451/144115188075855872)]
  L := [(9466553648078935782779/9444732965739290427392),(-3008331809/6597069766656),(74021649/1099511627776),(-3554005/412316860416),(56187/68719476736)]
  c := (2151593641/2147483648)
  R := (23900444071/25000000000000)
  total := (764216802139/250000000000000)
  k := 0
  n := 32
  sFloor := (2187099003241/288230376151711744)
  nFloor := 33503983554695734745113766081358992799231480581831077515760429165872939008
  eFloor := 33425406640231198047860227301603294287499813161186464071191111858114265088
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell239
