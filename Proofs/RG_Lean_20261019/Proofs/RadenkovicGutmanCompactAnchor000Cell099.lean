/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1603499/34359738368)
  b := (220481/4294967296)
  s := [(17177176329/17179869184),(-137840921/4398046511104),(-3442209/2199023255552)]
  L := [(132869383315100211240582291/1267650600228229401496703205376),(94393768057/4503599627370496),(28299882529/27021597764222976),(-37669/562949953421312),(-2821/1688849860263936)]
  c := (1888187502389/18014398509481984)
  R := (-458165462940517/100000000000000)
  total := (-21155667751/1000000000000000)
  k := 14
  n := 32
  sFloor := (1099303103721/2199023255552)
  nFloor := (1139935359079/9223372036854775808)
  eFloor := (852416858599/9223372036854775808)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell099
