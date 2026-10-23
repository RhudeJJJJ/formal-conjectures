/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (987115/2147483648)
  b := (542913/1073741824)
  s := [(4340252906059/4398046511104),(-1416349655/549755813888),(-128706883/1099511627776)]
  L := [(350336509300042581835791/38685626227668133590597632),(3017756349125/1688849860263936),(71404919131/844424930131968),(-48836567/105553116266496),(-494335/52776558133248)]
  c := (159314599523/17592186044416)
  R := (-117608231174899/50000000000000)
  total := (-105926140519/1000000000000000)
  k := 7
  n := 32
  sFloor := (2164203640643/4398046511104)
  nFloor := (965469437701/72057594037927936)
  eFloor := (1410215952821/144115188075855872)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell123
