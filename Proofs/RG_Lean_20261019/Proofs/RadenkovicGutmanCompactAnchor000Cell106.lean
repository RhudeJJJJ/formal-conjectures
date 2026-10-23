/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell106
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (781189/8589934592)
  b := (859307/8589934592)
  s := [(2197715192457/2199023255552),(-130687881/1099511627776),(-6507017/1099511627776)]
  L := [(2017371050345323304396030517/5070602400912917605986812821504),(358135774759/4503599627370496),(837336517/211106232532992),(-135433/140737488355328),(-5035/211106232532992)]
  c := (447946357861/1125899906842624)
  R := (-97867746284029/25000000000000)
  total := (-3516096521/100000000000000)
  k := 12
  n := 32
  sFloor := (2197440802661/4398046511104)
  nFloor := (541109625635/1152921504606846976)
  eFloor := (1618516331297/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell106
