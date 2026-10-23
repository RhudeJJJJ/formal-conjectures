/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (337053/2199023255552)
  b := (1483033/8796093022208)
  s := [(1099511627443/1099511627776),(-67/1099511627776),(-3/1099511627776)]
  L := [(53861022156426118981687489825/340282366920938463463374607431768211456),(1195953164019/37778931862957161709568),(29898784731/18889465931478580854784),(-5/2361183241434822606848),(1/1180591620717411303424)]
  c := (1494943673197/9444732965739290427392)
  R := (-141041465847537/12500000000000)
  total := (-6888067/40000000000000)
  k := 33
  n := 32
  sFloor := (1099511627373/2199023255552)
  nFloor := (185049955195/151115727451828646838272)
  eFloor := (708061125745/604462909807314587353088)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell039
