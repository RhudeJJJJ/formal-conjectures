/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1173839/17179869184)
  b := (645611/8589934592)
  s := [(1099186033607/1099511627776),(-65089305/1099511627776),(-3247657/1099511627776)]
  L := [(3652709340363/18014398509481984),(730315268045/18014398509481984),(13676737735/6755399441055744),(-275941/1125899906842624),(-2575/422212465065984)]
  c := (1826354670181/9007199254740992)
  R := (-85034574570407/20000000000000)
  total := (-28719687731/1000000000000000)
  k := 13
  n := 32
  sFloor := (1099117696645/2199023255552)
  nFloor := (1365251588519/4611686018427387904)
  eFloor := (997076418693/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell103
