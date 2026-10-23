/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell164
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1535717/67108864)
  b := (211161/8388608)
  s := [(5411862880303/35184372088832),(-126245483457/17592186044416),(8364454897/8796093022208)]
  L := [(2302569549211502317835/2361183241434822606848),(44043911729/3298534883328),(-3561158705/1649267441664),(77218367/412316860416),(-680915/51539607552)]
  c := (1072217500401/1099511627776)
  R := (-1256858611769/100000000000000)
  total := (-21748991327/1000000000000000)
  k := 1
  n := 32
  sFloor := (324551858311/4398046511104)
  nFloor := (1084829573949/35184372088832)
  eFloor := (407922945277/17592186044416)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell164
