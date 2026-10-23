/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell142
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (754633/268435456)
  b := (51881/16777216)
  s := [(2009325157415/2199023255552),(-65750608391/4398046511104),(-681042939/2199023255552)]
  L := [(1782905215647893033835/37778931862957161709568),(1201922419945/140737488355328),(56483577565/211106232532992),(-109297919/8796093022208),(959831/13194139533312)]
  c := (415114968933/8796093022208)
  R := (-9542210661543/6250000000000)
  total := (-41696495603/100000000000000)
  k := 5
  n := 32
  sFloor := (246971101285/549755813888)
  nFloor := (13368929171/35184372088832)
  eFloor := (204309853581/562949953421312)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell142
