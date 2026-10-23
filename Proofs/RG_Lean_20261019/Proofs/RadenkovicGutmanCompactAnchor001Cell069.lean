/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell069
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (735163/274877906944)
  b := (808679/274877906944)
  s := [(1099511528413/1099511627776),(-621/34359738368),(-497/549755813888)]
  L := [(245613085963377317610663397/5192296858534827628530496329220096),(2094214374659/221360928884514619392),(52355124859/110680464442257309696),(-245/13835058055282163712),(-7/6917529027641081856)]
  c := (436296485097/9223372036854775808)
  R := (-843334225719697/100000000000000)
  total := (-2242548253/1000000000000000)
  k := 25
  n := 32
  sFloor := (1099511507547/2199023255552)
  nFloor := (811420077011/2361183241434822606848)
  eFloor := (387541211339/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell069
