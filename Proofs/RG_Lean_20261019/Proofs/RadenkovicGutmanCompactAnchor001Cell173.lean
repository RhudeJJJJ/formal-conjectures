/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell173
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (905281/16777216)
  b := (995809/16777216)
  s := [(2546521146229/8796093022208),(9193829095/4398046511104),(1696624555/4398046511104)]
  L := [(2785061151529374139733/4722366482869645213696),(-3959758519/13194139533312),(-2011353125/3298534883328),(52854803/412316860416),(-143785/12884901888)]
  c := (1295151652191/2199023255552)
  R := (-13234637319877/50000000000000)
  total := (-11408830303/8000000000000)
  k := 1
  n := 32
  sFloor := (636630286557/4398046511104)
  nFloor := (1600270816415/8796093022208)
  eFloor := (1495049399803/8796093022208)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell173
