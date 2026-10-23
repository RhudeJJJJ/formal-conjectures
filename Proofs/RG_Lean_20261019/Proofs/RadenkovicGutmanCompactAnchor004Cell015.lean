/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell015
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1095033/70368744177664)
  b := (150567/8796093022208)
  s := [(4398046511041/4398046511104),(-11/4398046511104),(-1/2199023255552)]
  L := [(2980001117275/302231454903657293676544),(893997885911/453347182355485940514816),(5587471489/56668397794435742564352),(-1/3541774862152233910272),(1/7083549724304467820544)]
  c := (1490000558637/151115727451828646838272)
  R := (-126712676461529/10000000000000)
  total := (-19642829/1000000000000000)
  k := 37
  n := 32
  sFloor := (1099511627757/2199023255552)
  nFloor := (328053536809/19342813113834066795298816)
  eFloor := (1880824852595/154742504910672534362390528)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell015
