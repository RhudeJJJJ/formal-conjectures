/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1923603/2147483648)
  b := (1057981/1073741824)
  s := [(4190090099907/4398046511104),(-19334337745/2199023255552),(-330029431/1099511627776)]
  L := [(1252570293234322975007/37778931862957161709568),(2664383427463/422212465065984),(53881261543/211106232532992),(-140571823/26388279066624),(-589423/13194139533312)]
  c := (1166546990381/35184372088832)
  R := (-170327695718841/100000000000000)
  total := (-4639253439/31250000000000)
  k := 5
  n := 32
  sFloor := (1037525326673/2199023255552)
  nFloor := (916632211771/18014398509481984)
  eFloor := (167361693059/4503599627370496)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell130
