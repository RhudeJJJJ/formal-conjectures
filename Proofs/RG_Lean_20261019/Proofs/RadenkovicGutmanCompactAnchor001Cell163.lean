/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell163
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1396107/67108864)
  b := (1535717/67108864)
  s := [(3143094153373/8796093022208),(-160905327041/8796093022208),(4295999311/2199023255552)]
  L := [(587332407775494217151/1180591620717411303424),(562549658147/26388279066624),(-9729415073/4398046511104),(250429321/1649267441664),(-2069647/274877906944)]
  c := (1093991860329/2199023255552)
  R := (-34909001167069/100000000000000)
  total := (-176419217953/250000000000000)
  k := 2
  n := 32
  sFloor := (374921602947/2199023255552)
  nFloor := (762066434351/35184372088832)
  eFloor := (90661461231/4398046511104)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell163
