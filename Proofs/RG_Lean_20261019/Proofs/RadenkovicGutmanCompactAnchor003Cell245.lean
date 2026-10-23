/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell245
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (422391/8192)
  b := (232315/4096)
  s := [(4198846106307/1152921504606846976),(-310369717429/288230376151711744),(24766087063/144115188075855872)]
  L := [(151228151305429472334241/151115727451828646838272),(-975403855/6597069766656),(72576121/3298534883328),(-1171619/412316860416),(55991/206158430208)]
  c := (550094209001/549755813888)
  R := (15383693987/50000000000000)
  total := (872004564851/500000000000000)
  k := 0
  n := 32
  sFloor := (1577747966547/1152921504606846976)
  nFloor := 84221257058133265837766752684243518759868208488363638861794610274146839504803766206464
  eFloor := 84158033498756625536120963253143984148631540838120590006851194975870419471681158381568
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell245
