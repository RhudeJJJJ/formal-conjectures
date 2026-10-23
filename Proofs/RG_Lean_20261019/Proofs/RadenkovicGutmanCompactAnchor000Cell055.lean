/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1548741/2199023255552)
  b := (851807/1099511627776)
  s := [(4398046354061/4398046511104),(-15703/2199023255552),(-393/1099511627776)]
  L := [(3523422054615/147573952589676412928),(2114038140679/442721857769029238784),(17616856841/73786976294838206464),(-7/1729382256910270464),(1/4611686018427387904)]
  c := (1761711027307/73786976294838206464)
  R := (-877520364481361/100000000000000)
  total := (-307305833/500000000000000)
  k := 26
  n := 32
  sFloor := (2199023160541/4398046511104)
  nFloor := (1063409075945/37778931862957161709568)
  eFloor := (1590384567901/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell055
