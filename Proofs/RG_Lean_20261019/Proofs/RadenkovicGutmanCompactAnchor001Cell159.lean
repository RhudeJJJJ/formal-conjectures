/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell159
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1907125/134217728)
  b := (524459/33554432)
  s := [(3921955572421/8796093022208),(-244341092129/8796093022208),(10005876431/4398046511104)]
  L := [(3795861663332297957271/9444732965739290427392),(1482208516573/52776558133248),(-51967994587/26388279066624),(279085115/3298534883328),(-2343941/1649267441664)]
  c := (1767585828589/4398046511104)
  R := (-22788644766617/50000000000000)
  total := (-624416397429/1000000000000000)
  k := 2
  n := 32
  sFloor := (1848813116577/8796093022208)
  nFloor := (173939375261/17592186044416)
  eFloor := (331729809655/35184372088832)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell159
