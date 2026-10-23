/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1923603/2147483648)
  b := (1057981/1073741824)
  s := [(2082165609315/2199023255552),(-43064309597/4398046511104),(-695710659/2199023255552)]
  L := [(2758015527968995885711/75557863725914323419136),(971775751013/140737488355328),(57296016805/211106232532992),(-56470191/8796093022208),(-545977/13194139533312)]
  c := (80268816323/2199023255552)
  R := (-33103873601707/20000000000000)
  total := (-144175836961/1000000000000000)
  k := 5
  n := 32
  sFloor := (2059937743857/4398046511104)
  nFloor := (1640583339749/36028797018963968)
  eFloor := (1226800678445/36028797018963968)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell130
