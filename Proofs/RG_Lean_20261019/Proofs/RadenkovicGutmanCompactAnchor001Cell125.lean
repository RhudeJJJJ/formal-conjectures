/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (149301/268435456)
  b := (164231/268435456)
  s := [(4380964541341/4398046511104),(-1697696499/2199023255552),(-41227083/1099511627776)]
  L := [(1260842910038578584873659/618970019642690137449562112),(2740390128727/6755399441055744),(67341016835/3377699720527872),(-14455807/422212465065984),(-169979/211106232532992)]
  c := (71670621653/35184372088832)
  R := (-309813818222923/100000000000000)
  total := (-84817019207/500000000000000)
  k := 9
  n := 32
  sFloor := (2188702120005/4398046511104)
  nFloor := (267735938091/18014398509481984)
  eFloor := (1022981189509/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell125
