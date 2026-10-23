/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell019
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1603235/70368744177664)
  b := (881779/35184372088832)
  s := [(2199023255485/2199023255552),(-3/549755813888),(-1/1099511627776)]
  L := [(6387874614283/302231454903657293676544),(3832712815331/906694364710971881029632),(95817521579/453347182355485940514816),(-5/56668397794435742564352),(1/28334198897217871282176)]
  c := (798484326785/37778931862957161709568)
  R := (-614501434147723/50000000000000)
  total := (-13945209/500000000000000)
  k := 36
  n := 32
  sFloor := (2199023255471/4398046511104)
  nFloor := (351604710447/9671406556917033397649408)
  eFloor := (1007925237037/38685626227668133590597632)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell019
