/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell217
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (468645/131072)
  b := (1031019/262144)
  s := [(4686238759695/562949953421312),(-586811144485/281474976710656),(19886270743/70368744177664)]
  L := [(651058612851737701489/590295810358705651712),(-182916993221/13194139533312),(2444089259/2199023255552),(-33110131/824633720832),(-372251/137438953472)]
  c := (1198623004105/1099511627776)
  R := (4315364743361/100000000000000)
  total := (16446104447393/1000000000000000)
  k := 0
  n := 32
  sFloor := (917926659167/281474976710656)
  nFloor := 4499322731058925478743986143232
  eFloor := 4012047625483942572639001772032
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell217
