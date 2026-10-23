/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (602367/17179869184)
  b := (1325207/34359738368)
  s := [(2198988409655/2199023255552),(-13937963/4398046511104),(-348407/2199023255552)]
  L := [(83996859403726450395052249/10141204801825835211973625643008),(2864741951963/1729382256910270464),(23871112541/288230376151711744),(-62135/108086391056891904),(-261/18014398509481984)]
  c := (1193667165519/144115188075855872)
  R := (-117013379557243/20000000000000)
  total := (-20344046773/1000000000000000)
  k := 17
  n := 32
  sFloor := (1099490546133/2199023255552)
  nFloor := (1182074880733/18446744073709551616)
  eFloor := (1130750423883/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell096
