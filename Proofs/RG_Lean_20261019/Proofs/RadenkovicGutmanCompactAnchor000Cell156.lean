/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell156
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (358213/33554432)
  b := (1576137/134217728)
  s := [(1129760962695/4398046511104),(-180291066687/8796093022208),(3971051677/2199023255552)]
  L := [(3729088177236577760237/4722366482869645213696),(304294283745/8796093022208),(-38533787743/13194139533312),(110880393/549755813888),(-9353117/824633720832)]
  c := (217061500137/274877906944)
  R := (-368978594023/3125000000000)
  total := (-57565539937/500000000000000)
  k := 1
  n := 32
  sFloor := (2095115065411/17592186044416)
  nFloor := (917572990863/140737488355328)
  eFloor := (1374025319943/281474976710656)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell156
