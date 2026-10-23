/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (837135/8796093022208)
  b := (1841697/17592186044416)
  s := [(137438953393/137438953472),(-509/4398046511104),(-11/2199023255552)]
  L := [(1858319806955/4722366482869645213696),(2229983767031/28334198897217871282176),(55749594059/14167099448608935641088),(-5/1770887431076116955136),(1/885443715538058477568)]
  c := (1858319806955/4722366482869645213696)
  R := (-270698789181307/25000000000000)
  total := (-5129513/50000000000000)
  k := 32
  n := 32
  sFloor := (1099511627011/2199023255552)
  nFloor := (694362812767/1208925819614629174706176)
  eFloor := (1014220007647/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell034
