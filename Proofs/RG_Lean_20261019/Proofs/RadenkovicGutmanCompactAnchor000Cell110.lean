/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell110
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (142967/1073741824)
  b := (1258109/8589934592)
  s := [(4392444425545/4398046511104),(-1118267053/4398046511104),(-27706579/2199023255552)]
  L := [(16880461587840666386515321/19807040628566084398385987584),(1533268518291/9007199254740992),(38132587475/4503599627370496),(-2478677/562949953421312),(-30407/281474976710656)]
  c := (959543148601/1125899906842624)
  R := (-88345448834163/25000000000000)
  total := (-46408349193/1000000000000000)
  k := 11
  n := 32
  sFloor := (2195635372667/4398046511104)
  nFloor := (1159911604619/1152921504606846976)
  eFloor := (867354776897/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell110
