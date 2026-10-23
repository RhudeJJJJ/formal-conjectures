/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell234
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (592185/32768)
  b := (1302807/65536)
  s := [(3014479189507/36028797018963968),(-442545662835/18014398509481984),(70142868945/18014398509481984)]
  L := [(19000678260371878185887/18889465931478580854784),(-15139590341/13194139533312),(1100570267/6597069766656),(-17311999/824633720832),(808309/412316860416)]
  c := (276221476495/274877906944)
  R := (243798533137/100000000000000)
  total := (2417218844901/500000000000000)
  k := 0
  n := 32
  sFloor := (1134836800863/36028797018963968)
  nFloor := 15282101889086287064415848563120830445452880225720109891584
  eFloor := 15190112557178962362849892938360471720213762534350469988352
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell234
