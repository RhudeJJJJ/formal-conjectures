/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1225845/4294967296)
  b := (1348429/4294967296)
  s := [(2196763800313/2199023255552),(-902309257/4398046511104),(-22386299/2199023255552)]
  L := [(21316448486399507933905399/39614081257132168796771975168),(2904785508601/27021597764222976),(24097190925/4503599627370496),(-4086145/1688849860263936),(-16757/281474976710656)]
  c := (1211699809937/2251799813685248)
  R := (-376373045861491/100000000000000)
  total := (-106041894581/1000000000000000)
  k := 11
  n := 32
  sFloor := (2196290259385/4398046511104)
  nFloor := (564017996297/144115188075855872)
  eFloor := (1077518641557/288230376151711744)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell118
