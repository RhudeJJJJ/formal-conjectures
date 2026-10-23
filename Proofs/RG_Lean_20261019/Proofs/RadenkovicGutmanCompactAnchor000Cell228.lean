/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell228
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1337095/131072)
  b := (367701/32768)
  s := [(4082724631163/9007199254740992),(-1179053776647/9007199254740992),(91929865057/4503599627370496)]
  L := [(600710217008783622483/590295810358705651712),(-10930386305/3298534883328),(1515804923/3298534883328),(-22538429/412316860416),(997135/206158430208)]
  c := (557858496793/549755813888)
  R := (91444595961/12500000000000)
  total := (1019948490473/125000000000000)
  k := 0
  n := 32
  sFloor := (1543765292315/9007199254740992)
  nFloor := 728414822676141778063753565431230774539976704
  eFloor := 715137822533550574069388880305766448863641600
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell228
