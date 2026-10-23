/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell180
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (882065/8388608)
  b := (1940543/16777216)
  s := [(2764377396103/8796093022208),(47321126579/17592186044416),(-5667202441/8796093022208)]
  L := [(2753845052728285610979/4722366482869645213696),(198950975/103079215104),(2815729343/3298534883328),(-10367279/412316860416),(-534851/206158430208)]
  c := (1282359032299/2199023255552)
  R := (-26965595567187/100000000000000)
  total := (-564850775873/200000000000000)
  k := 1
  n := 32
  sFloor := (1382188698051/8796093022208)
  nFloor := (709734454711/549755813888)
  eFloor := (158752814785/137438953472)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell180
