/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (837135/8796093022208)
  b := (1841697/17592186044416)
  s := [(549755813825/549755813888),(-99/4398046511104),(-3/2199023255552)]
  L := [(4525801075383/75557863725914323419136),(1357740322441/113336795588871485128704),(2828625671/4722366482869645213696),(-1/7083549724304467820544)]
  c := (1131450268845/18889465931478580854784)
  R := (-58845925029777/5000000000000)
  total := (-22309619/200000000000000)
  k := 34
  n := 32
  sFloor := (2199023255247/4398046511104)
  nFloor := (1052130150025/2417851639229258349412352)
  eFloor := (502506413637/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell034
