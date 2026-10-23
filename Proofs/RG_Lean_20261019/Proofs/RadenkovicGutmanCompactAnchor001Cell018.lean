/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1457487/70368744177664)
  b := (1603235/70368744177664)
  s := [(549755813885/549755813888),(-7/4398046511104),(1/2199023255552)]
  L := [(857420491597/302231454903657293676544),(2057799296591/3626777458843887524118528),(17148245127/604462909807314587353088),(-11/226673591177742970257408),(1/37778931862957161709568)]
  c := (857420491597/302231454903657293676544)
  R := (-132941428965789/10000000000000)
  total := (-27434619/1000000000000000)
  k := 39
  n := 32
  sFloor := (2199023255537/4398046511104)
  nFloor := (99663897653/4835703278458516698824704)
  eFloor := (761605362645/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell018
