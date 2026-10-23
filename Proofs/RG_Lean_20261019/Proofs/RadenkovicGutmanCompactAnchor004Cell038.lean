/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (76603/549755813888)
  b := (337053/2199023255552)
  s := [(549755813265/549755813888),(-997/4398046511104),(-25/2199023255552)]
  L := [(65677005435687102633165269/83076749736557242056487941267521536),(4479937388815/28334198897217871282176),(111997703011/14167099448608935641088),(23/1770887431076116955136),(-7/885443715538058477568)]
  c := (116665797797/147573952589676412928)
  R := (-104791409211183/10000000000000)
  total := (-908381/6250000000000)
  k := 31
  n := 32
  sFloor := (274877906567/549755813888)
  nFloor := (821962164543/604462909807314587353088)
  eFloor := (1178136106993/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell038
