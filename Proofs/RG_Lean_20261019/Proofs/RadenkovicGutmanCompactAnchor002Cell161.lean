/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell161
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1153809/67108864)
  b := (1269189/67108864)
  s := [(3382378055483/17592186044416),(-432211930797/35184372088832),(22949938189/17592186044416)]
  L := [(4361715340202043113907/4722366482869645213696),(302116928929/13194139533312),(-5894175811/2199023255552),(177144731/824633720832),(-1954333/137438953472)]
  c := (507770495047/549755813888)
  R := (-158889281601/4000000000000)
  total := (-58496177099/1000000000000000)
  k := 1
  n := 32
  sFloor := (199326376767/2199023255552)
  nFloor := (675762762475/35184372088832)
  eFloor := (991338299509/70368744177664)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell161
