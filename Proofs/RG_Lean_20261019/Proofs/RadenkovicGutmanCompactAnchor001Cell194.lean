/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell194
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (418703/1048576)
  b := (460573/1048576)
  s := [(999867463219/4398046511104),(-238405329263/17592186044416),(3667577921/8796093022208)]
  L := [(7896478620830225212739/9444732965739290427392),(912876985391/26388279066624),(-4393401223/4398046511104),(-31895603/1649267441664),(849591/274877906944)]
  c := (919271099943/1099511627776)
  R := (-4476007802519/50000000000000)
  total := (-3174917448519/1000000000000000)
  k := 1
  n := 32
  sFloor := (1884199839727/17592186044416)
  nFloor := (39350429321/8388608)
  eFloor := (948147645835/268435456)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell194
