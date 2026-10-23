/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (837135/8796093022208)
  b := (1841697/17592186044416)
  s := [(1099511627059/1099511627776),(-287/2199023255552),(-7/1099511627776)]
  L := [(4117732059627/9444732965739290427392),(2470639234123/28334198897217871282176),(61765980719/14167099448608935641088),(-7/1770887431076116955136),(1/885443715538058477568)]
  c := (2058866029813/4722366482869645213696)
  R := (-134708878275721/12500000000000)
  total := (-10210259/100000000000000)
  k := 32
  n := 32
  sFloor := (2199023253817/4398046511104)
  nFloor := (621389294285/1208925819614629174706176)
  eFloor := (1858641169497/4835703278458516698824704)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell034
