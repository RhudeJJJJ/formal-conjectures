/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell138
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (515425/268435456)
  b := (1133935/536870912)
  s := [(4207300780163/4398046511104),(-35559573521/4398046511104),(-615938425/2199023255552)]
  L := [(28054185955358819714073/1208925819614629174706176),(19437588563/4398046511104),(18914347181/105553116266496),(-4079985/1099511627776),(-220109/6597069766656)]
  c := (408242135823/17592186044416)
  R := (-188167481958319/100000000000000)
  total := (-352478515471/1000000000000000)
  k := 6
  n := 32
  sFloor := (32582104139/68719476736)
  nFloor := (797979563827/4503599627370496)
  eFloor := (95277463907/562949953421312)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell138
