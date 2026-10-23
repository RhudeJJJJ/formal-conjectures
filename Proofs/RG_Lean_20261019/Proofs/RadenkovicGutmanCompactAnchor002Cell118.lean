/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1225845/4294967296)
  b := (1348429/4294967296)
  s := [(4375488176461/4398046511104),(-2238428293/2199023255552),(-53950307/1099511627776)]
  L := [(2179143338791129510084169/618970019642690137449562112),(2365830919859/3377699720527872),(57907374187/1688849860263936),(-15279659/211106232532992),(-176707/105553116266496)]
  c := (990959660517/281474976710656)
  R := (-282456250113251/100000000000000)
  total := (-79242864389/1000000000000000)
  k := 9
  n := 32
  sFloor := (2185397759323/4398046511104)
  nFloor := (1488913590371/288230376151711744)
  eFloor := (1087391033579/288230376151711744)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell118
