/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell024
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (645505/17592186044416)
  b := (1420111/35184372088832)
  s := [(2199023255379/2199023255552),(-67/4398046511104),(-3/2199023255552)]
  L := [(1165899233210788032563274147/21267647932558653966460912964485513216),(2485263692173/226673591177742970257408),(20710530745/37778931862957161709568),(11/14167099448608935641088),(-1/2361183241434822606848)]
  c := (2071053076965/37778931862957161709568)
  R := (-1181348010765871/100000000000000)
  total := (-21584623/500000000000000)
  k := 35
  n := 32
  sFloor := (1099511627671/2199023255552)
  nFloor := (1823935656733/19342813113834066795298816)
  eFloor := (81696447945/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell024
