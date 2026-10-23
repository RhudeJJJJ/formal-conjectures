/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell234
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (592185/32768)
  b := (1302807/65536)
  s := [(3014479189507/36028797018963968),(-442545662835/18014398509481984),(70142868945/18014398509481984)]
  L := [(19000678260395663021975/18889465931478580854784),(-15139590341/13194139533312),(1100570267/6597069766656),(-17311999/824633720832),(808309/412316860416)]
  c := (1104885905981/1099511627776)
  R := (243798533183/100000000000000)
  total := (4834437690947/1000000000000000)
  k := 0
  n := 32
  sFloor := (1134836800863/36028797018963968)
  nFloor := 5021660196088383811953061292165731187966916740534639100166144
  eFloor := 4991432733278081606363473441065238896163255166286806017638400
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell234
