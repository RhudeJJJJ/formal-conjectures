/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell136
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (851943/536870912)
  b := (937137/536870912)
  s := [(7660333009303/8796093022208),(-184611273913/8796093022208),(-927404603/4398046511104)]
  L := [(28560028175034091297175/302231454903657293676544),(1731316771361/105553116266496),(21126686879/52776558133248),(-5960245/206158430208),(1704427/3298534883328)]
  c := (1662412435691/17592186044416)
  R := (-29489812585117/25000000000000)
  total := (-36114533053/200000000000000)
  k := 4
  n := 32
  sFloor := (934233365773/2199023255552)
  nFloor := (1438589177661/9007199254740992)
  eFloor := (525338071289/4503599627370496)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell136
