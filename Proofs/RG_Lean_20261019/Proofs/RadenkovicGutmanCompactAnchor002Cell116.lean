/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell116
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (126637/536870912)
  b := (1114405/4294967296)
  s := [(4382600684809/4398046511104),(-768207157/1099511627776),(-37463835/1099511627776)]
  L := [(745432204509349140031029/309485009821345068724781056),(1621272419507/3377699720527872),(832299639/35184372088832),(-3600697/105553116266496),(-14233/17592186044416)]
  c := (169491660133/70368744177664)
  R := (-75358759324453/25000000000000)
  total := (-8745573651/125000000000000)
  k := 9
  n := 32
  sFloor := (547422250105/1099511627776)
  nFloor := (254236943339/72057594037927936)
  eFloor := (46418890187/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell116
