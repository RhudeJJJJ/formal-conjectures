/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (881779/35184372088832)
  b := (242489/8796093022208)
  s := [(4398046511069/4398046511104),(-1/549755813888)]
  L := [(2510695067407/604462909807314587353088),(753200832485/906694364710971881029632),(9414914317/226673591177742970257408),(-7/113336795588871485128704),(1/28334198897217871282176)]
  c := (1255347533703/302231454903657293676544)
  R := (-1310352325710663/100000000000000)
  total := (-32717967/1000000000000000)
  k := 38
  n := 32
  sFloor := (1099511627765/2199023255552)
  nFloor := (583670809571/19342813113834066795298816)
  eFloor := (1115064805453/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell020
