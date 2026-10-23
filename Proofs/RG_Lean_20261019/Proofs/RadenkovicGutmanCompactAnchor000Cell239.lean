/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell239
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (476859/16384)
  b := (1049089/32768)
  s := [(5817205770727/288230376151711744),(-1716354747147/288230376151711744),(136673491451/144115188075855872)]
  L := [(37866214592200405904923/37778931862957161709568),(-3008331809/6597069766656),(74021649/1099511627776),(-3554005/412316860416),(56187/68719476736)]
  c := (1101615944189/1099511627776)
  R := (23900444037/25000000000000)
  total := (95527100129/31250000000000)
  k := 0
  n := 32
  sFloor := (2187099003241/288230376151711744)
  nFloor := 54727207573240664995280417395170361981631964271193139604187250688
  eFloor := 54598855817627965915997073003701137691865753156839353710603665408
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell239
