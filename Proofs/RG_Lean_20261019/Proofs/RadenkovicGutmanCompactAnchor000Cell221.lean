/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell221
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1372285/262144)
  b := (1509513/262144)
  s := [(3419735844357/1125899906842624),(-1856821819483/2251799813685248),(136237300455/1125899906842624)]
  L := [(19983535511116800517793/18889465931478580854784),(-125550515365/13194139533312),(2396879153/2199023255552),(-81797465/824633720832),(871963/137438953472)]
  c := (576914333965/549755813888)
  R := (482195825959/20000000000000)
  total := (13641110014643/1000000000000000)
  k := 0
  n := 32
  sFloor := (1313781117535/1125899906842624)
  nFloor := 390515833461365572051621946327040
  eFloor := 366900070248031553525549262438400
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell221
