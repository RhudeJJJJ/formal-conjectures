/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1348429/4294967296)
  b := (1483271/4294967296)
  s := [(1091792905231/1099511627776),(-1527477359/1099511627776),(-72632333/1099511627776)]
  L := [(728920291270180967502553/154742504910672534362390528),(789843206177/844424930131968),(38363909741/844424930131968),(-13854259/105553116266496),(-155507/52776558133248)]
  c := (662949142925/140737488355328)
  R := (-53579533696311/20000000000000)
  total := (-82599275419/1000000000000000)
  k := 8
  n := 32
  sFloor := (1090192795539/2199023255552)
  nFloor := (1612248425405/288230376151711744)
  eFloor := (37675086569/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell119
