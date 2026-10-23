/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1445001/4398046511104)
  b := (1589501/4398046511104)
  s := [(4398046505105/4398046511104),(-1197/4398046511104),(-31/2199023255552)]
  L := [(3371170865273/4722366482869645213696),(2022701116363/14167099448608935641088),(16855830851/2361183241434822606848),(1/110680464442257309696),(-1/147573952589676412928)]
  c := (421396358159/590295810358705651712)
  R := (-52650789406499/5000000000000)
  total := (-344383151/1000000000000000)
  k := 31
  n := 32
  sFloor := (2199023251923/4398046511104)
  nFloor := (783708884695/151115727451828646838272)
  eFloor := (748612214893/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell047
