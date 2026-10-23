/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell022
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1066951/35184372088832)
  b := (586823/17592186044416)
  s := [(1099511627703/1099511627776),(-55/4398046511104),(-3/2199023255552)]
  L := [(1672230123549/37778931862957161709568),(2006674267387/226673591177742970257408),(50166809617/113336795588871485128704),(5/14167099448608935641088),(-1/7083549724304467820544)]
  c := (1672230123549/37778931862957161709568)
  R := (-1192042964358697/100000000000000)
  total := (-36001369/1000000000000000)
  k := 35
  n := 32
  sFloor := (2199023255375/4398046511104)
  nFloor := (504698159417/9671406556917033397649408)
  eFloor := (754802815151/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell022
