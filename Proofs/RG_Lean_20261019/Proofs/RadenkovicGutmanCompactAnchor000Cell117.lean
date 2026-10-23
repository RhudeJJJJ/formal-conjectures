/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1114405/4294967296)
  b := (1225845/4294967296)
  s := [(4376887143197/4398046511104),(-4201294681/4398046511104),(-101497971/2199023255552)]
  L := [(498995176822762332452813/154742504910672534362390528),(4335424663021/6755399441055744),(106262421041/3377699720527872),(-26217025/422212465065984),(-304745/211106232532992)]
  c := (907666939061/281474976710656)
  R := (-2240984892899/781250000000)
  total := (-7317752573/100000000000000)
  k := 9
  n := 32
  sFloor := (2186241426287/4398046511104)
  nFloor := (1101186650565/288230376151711744)
  eFloor := (411721044153/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell117
