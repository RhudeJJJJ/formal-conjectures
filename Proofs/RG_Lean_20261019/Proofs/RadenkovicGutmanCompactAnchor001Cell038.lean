/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (76603/549755813888)
  b := (337053/2199023255552)
  s := [(4398046510025/4398046511104),(-217/4398046511104),(-5/2199023255552)]
  L := [(4850717556607/37778931862957161709568),(727602884089/28334198897217871282176),(36379906681/28334198897217871282176),(1/885443715538058477568),(-1/1770887431076116955136)]
  c := (1212679389151/9444732965739290427392)
  R := (-113879453911231/10000000000000)
  total := (-158004163/1000000000000000)
  k := 33
  n := 32
  sFloor := (2199023254899/4398046511104)
  nFloor := (35239522423/37778931862957161709568)
  eFloor := (1077164746169/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell038
