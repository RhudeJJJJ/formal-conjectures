/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (874365/1073741824)
  b := (1923603/2147483648)
  s := [(4361687662079/4398046511104),(-7176832395/4398046511104),(-168536803/2199023255552)]
  L := [(1344804487156193678078183/309485009821345068724781056),(363594530197/422212465065984),(11680252137/281474976710656),(-16129501/105553116266496),(-58751/17592186044416)]
  c := (1223092555989/281474976710656)
  R := (-135966525440991/50000000000000)
  total := (-21753576147/100000000000000)
  k := 8
  n := 32
  sFloor := (2177086878039/4398046511104)
  nFloor := (286966636677/9007199254740992)
  eFloor := (548227822227/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell129
