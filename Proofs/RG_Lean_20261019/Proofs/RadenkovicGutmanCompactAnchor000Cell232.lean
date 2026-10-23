/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell232
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (978819/65536)
  b := (269175/16384)
  s := [(5309989382545/36028797018963968),(-194173700773/4503599627370496),(61331562473/9007199254740992)]
  L := [(4762618472407351407139/4722366482869645213696),(-5432837701/3298534883328),(781489111/3298534883328),(-6070817/206158430208),(560417/206158430208)]
  c := (553651843039/549755813888)
  R := (35309210677/10000000000000)
  total := (1445414021681/250000000000000)
  k := 0
  n := 32
  sFloor := (1000481506563/18014398509481984)
  nFloor := 11266196147871189381114439625101724424723471978725376
  eFloor := 11167685863531501807302598970963850172417520527474688
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell232
