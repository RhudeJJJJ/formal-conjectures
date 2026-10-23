/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell108
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (945237/8589934592)
  b := (64985/536870912)
  s := [(4394941809405/4398046511104),(-620275033/4398046511104),(-15429643/2199023255552)]
  L := [(624552866686292157132696197/1267650600228229401496703205376),(2660685076675/27021597764222976),(66324386053/13510798882111488),(-2398855/1688849860263936),(-29677/844424930131968)]
  c := (1109428756305/2251799813685248)
  R := (-38078199218667/10000000000000)
  total := (-20684361121/500000000000000)
  k := 11
  n := 32
  sFloor := (2197145337543/4398046511104)
  nFloor := (1955519832325/2305843009213693952)
  eFloor := (700722354189/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell108
