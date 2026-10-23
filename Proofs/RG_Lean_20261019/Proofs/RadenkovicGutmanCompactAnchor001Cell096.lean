/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (602367/17179869184)
  b := (1325207/34359738368)
  s := [(2198989101815/2199023255552),(-3415279/1099511627776),(-170743/1099511627776)]
  L := [(2343254154433/288230376151711744),(1405923839549/864691128455135232),(5857596817/72057594037927936),(-14995/27021597764222976),(-31/2251799813685248)]
  c := (36613346163/4503599627370496)
  R := (-146499684112119/25000000000000)
  total := (-10188359543/500000000000000)
  k := 17
  n := 32
  sFloor := (2198981929771/4398046511104)
  nFloor := (544754542231/9223372036854775808)
  eFloor := (520358908897/9223372036854775808)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell096
