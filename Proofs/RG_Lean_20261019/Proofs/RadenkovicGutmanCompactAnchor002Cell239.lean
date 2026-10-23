/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell239
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (476859/16384)
  b := (1049089/32768)
  s := [(5817205770727/288230376151711744),(-1716354747147/288230376151711744),(136673491451/144115188075855872)]
  L := [(75732429184563227376505/75557863725914323419136),(-3008331809/6597069766656),(74021649/1099511627776),(-3554005/412316860416),(56187/68719476736)]
  c := (1101615944191/1099511627776)
  R := (95601776239/100000000000000)
  total := (382108400907/125000000000000)
  k := 0
  n := 32
  sFloor := (2187099003241/288230376151711744)
  nFloor := 39457726747100239495198350353151540023184620293625267899934379194974208
  eFloor := 39365186514857642391507020017531126745951263043204376509163264523894784
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell239
