/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell223
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (103779/16384)
  b := (913255/131072)
  s := [(502977874399/281474976710656),(-2241182925773/4503599627370496),(168609868485/2251799813685248)]
  L := [(9840895325088229469573/9444732965739290427392),(-48091402999/6597069766656),(187229095/206158430208),(-2417213/25769803776),(733411/103079215104)]
  c := (35578718947/34359738368)
  R := (1743109703777/100000000000000)
  total := (11988604098939/1000000000000000)
  k := 0
  n := 32
  sFloor := (1535920700395/2251799813685248)
  nFloor := 3389680370702158983911642179519973941051392
  eFloor := 3241617019240628194300290123916834586492928
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell223
