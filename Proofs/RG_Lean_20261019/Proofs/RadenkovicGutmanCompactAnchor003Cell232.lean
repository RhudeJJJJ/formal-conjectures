/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell232
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (978819/65536)
  b := (269175/16384)
  s := [(5309989382545/36028797018963968),(-194173700773/4503599627370496),(61331562473/9007199254740992)]
  L := [(9525236944906262001853/9444732965739290427392),(-5432837701/3298534883328),(781489111/3298534883328),(-6070817/206158430208),(560417/206158430208)]
  c := (1107303686089/1099511627776)
  R := (353092107267/100000000000000)
  total := (722707011739/125000000000000)
  k := 0
  n := 32
  sFloor := (1000481506563/18014398509481984)
  nFloor := 128447008243535917422812871550626431539178473274253254852608
  eFloor := 127323882821447971931339460440820000205698103315993215369216
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell232
