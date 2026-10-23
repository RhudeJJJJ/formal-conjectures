/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell236
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1433087/65536)
  b := (1576395/65536)
  s := [(3416532828797/72057594037927936),(-251414363263/18014398509481984),(79894382929/36028797018963968)]
  L := [(9483037085799218713705/9444732965739290427392),(-5247044945/6597069766656),(384353873/3298534883328),(-6098677/412316860416),(287023/206158430208)]
  c := (1103209692357/1099511627776)
  R := (8394316661/5000000000000)
  total := (2015336847623/500000000000000)
  k := 0
  n := 32
  sFloor := (1285332070801/72057594037927936)
  nFloor := 10405939614492028893011874002012598545117462043511903094473093617287168
  eFloor := 10362924936938812311515834132842045275279353766573592082802898754338816
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell236
