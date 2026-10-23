/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell251
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (374145/4096)
  b := (823119/8192)
  s := [(6047940560617/9223372036854775808),(-894705620389/4611686018427387904),(71440807815/2305843009213693952)]
  L := [(604606943794054540346477/604462909807314587353088),(-208923709/4398046511104),(46795997/6597069766656),(-252721/274877906944),(36343/412316860416)]
  c := (1099728278507/1099511627776)
  R := (123139551/1250000000000)
  total := (197906891313/200000000000000)
  k := 0
  n := 32
  sFloor := (568036568887/2305843009213693952)
  nFloor := 3123931064166794912783169912448450357303912616106029676194394375968518373901862599435223040
  eFloor := 3123182761962319316269222238459941443532453554599152061521650184801602902274690400221396992
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell251
