/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell139
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1133935/536870912)
  b := (38979/16777216)
  s := [(7036233842481/8796093022208),(-252103175263/8796093022208),(991872365/4398046511104)]
  L := [(91993708862848220800533/604462909807314587353088),(425722795919/17592186044416),(219362929/824633720832),(-54781115/1099511627776),(814387/412316860416)]
  c := (1338684652915/8796093022208)
  R := (-94131005928779/100000000000000)
  total := (-47696091987/250000000000000)
  k := 3
  n := 32
  sFloor := (1696528602987/4398046511104)
  nFloor := (39827376191/140737488355328)
  eFloor := (1861685728445/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell139
