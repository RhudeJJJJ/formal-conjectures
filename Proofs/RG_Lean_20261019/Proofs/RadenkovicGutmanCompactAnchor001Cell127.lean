/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(136659644759/137438953472),(-2471439061/2199023255552),(-29604161/549755813888)]
  L := [(1842348901881659418796245/618970019642690137449562112),(3996397013999/6755399441055744),(32474431979/1125899906842624),(-30622793/422212465065984),(-116559/70368744177664)]
  c := (837803282539/281474976710656)
  R := (-145425387584491/50000000000000)
  total := (-192502941901/1000000000000000)
  k := 9
  n := 32
  sFloor := (2183964460439/4398046511104)
  nFloor := (391996630625/18014398509481984)
  eFloor := (748880946865/36028797018963968)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell127
