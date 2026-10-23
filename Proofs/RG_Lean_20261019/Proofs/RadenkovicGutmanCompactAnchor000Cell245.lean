/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell245
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (422391/8192)
  b := (232315/4096)
  s := [(4198846106307/1152921504606846976),(-310369717429/288230376151711744),(24766087063/144115188075855872)]
  L := [(37807037826318532803075/37778931862957161709568),(-975403855/6597069766656),(72576121/3298534883328),(-1171619/412316860416),(55991/206158430208)]
  c := (68761776125/68719476736)
  R := (30767387883/100000000000000)
  total := (218001140881/125000000000000)
  k := 0
  n := 32
  sFloor := (1577747966547/1152921504606846976)
  nFloor := 4471910867634723796492608431962231812910643991425976186849356972458996924416
  eFloor := 4468553875202466723342245275586170059144750146271649965015018157668938285056
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell245
