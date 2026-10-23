/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (64985/536870912)
  b := (142967/1073741824)
  s := [(4393963057333/4398046511104),(-203887355/1099511627776),(-10127791/1099511627776)]
  L := [(100770462337696767121391243/158456325028528675187087900672),(858405659819/6755399441055744),(21378739387/3377699720527872),(-507589/211106232532992),(-12517/211106232532992)]
  c := (179004299983/281474976710656)
  R := (-718787988489/195312500000)
  total := (-21980604333/500000000000000)
  k := 11
  n := 32
  sFloor := (1098276749187/2199023255552)
  nFloor := (1071179348243/1152921504606846976)
  eFloor := (391154215391/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell109
