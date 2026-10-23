/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (448689/1073741824)
  b := (987115/2147483648)
  s := [(2194091358121/2199023255552),(-1965755963/4398046511104),(-48331121/2199023255552)]
  L := [(1452847559707657646497415/1237940039285380274899124224),(790859037377/3377699720527872),(39154121741/3377699720527872),(-2413817/211106232532992),(-58277/211106232532992)]
  c := (1321357158037/1125899906842624)
  R := (-337383927681333/100000000000000)
  total := (-868533401/6250000000000)
  k := 10
  n := 32
  sFloor := (1096530074509/2199023255552)
  nFloor := (1311752502459/144115188075855872)
  eFloor := (1254795535769/144115188075855872)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell122
