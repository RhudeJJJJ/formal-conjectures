/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell116
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (126637/536870912)
  b := (1114405/4294967296)
  s := [(4394958420709/4398046511104),(-616928279/4398046511104),(-15343033/2199023255552)]
  L := [(116517278238487931788965577/316912650057057350374175801344),(496356971111/6755399441055744),(8247049741/2251799813685248),(-477575/422212465065984),(-3937/140737488355328)]
  c := (1655810112857/4503599627370496)
  R := (-395417094497469/100000000000000)
  total := (-92129497287/1000000000000000)
  k := 12
  n := 32
  sFloor := (1098577701591/2199023255552)
  nFloor := (770463326133/288230376151711744)
  eFloor := (367979739069/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell116
