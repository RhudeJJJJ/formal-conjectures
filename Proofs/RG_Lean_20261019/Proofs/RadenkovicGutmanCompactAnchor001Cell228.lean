/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell228
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1337095/131072)
  b := (367701/32768)
  s := [(4082724631163/9007199254740992),(-1179053776647/9007199254740992),(91929865057/4503599627370496)]
  L := [(9611363472221379922125/9444732965739290427392),(-10930386305/3298534883328),(1515804923/3298534883328),(-22538429/412316860416),(997135/206158430208)]
  c := (278929248399/274877906944)
  R := (731556768137/100000000000000)
  total := (8159587928089/1000000000000000)
  k := 0
  n := 32
  sFloor := (1543765292315/9007199254740992)
  nFloor := 77253485655885664229796802596975652633801916416
  eFloor := 75845366946405374872848979277861487299528753152
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell228
