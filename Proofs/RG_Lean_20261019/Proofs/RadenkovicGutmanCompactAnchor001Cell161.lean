/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell161
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1153809/67108864)
  b := (1269189/67108864)
  s := [(1746263053219/4398046511104),(-51002745295/2199023255552),(2376197813/1099511627776)]
  L := [(34223909439759056449537/75557863725914323419136),(333271373875/13194139533312),(-7145637533/3298534883328),(25360565/206158430208),(-477941/103079215104)]
  c := (996046857901/2199023255552)
  R := (-19799356586201/50000000000000)
  total := (-26341849511/40000000000000)
  k := 2
  n := 32
  sFloor := (1653762353881/8796093022208)
  nFloor := (1027691315215/70368744177664)
  eFloor := (489607105351/35184372088832)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell161
