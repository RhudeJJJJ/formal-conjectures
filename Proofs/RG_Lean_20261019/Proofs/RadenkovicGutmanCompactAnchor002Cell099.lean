/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1603499/34359738368)
  b := (220481/4294967296)
  s := [(2198719397097/2199023255552),(-60758707/2199023255552),(-758741/549755813888)]
  L := [(119929311653494799011071397/1267650600228229401496703205376),(2044857456731/108086391056891904),(51092285347/54043195528445952),(-90167/1688849860263936),(-4501/3377699720527872)]
  c := (1704298024001/18014398509481984)
  R := (-463288666223991/100000000000000)
  total := (-21394751403/1000000000000000)
  k := 14
  n := 32
  sFloor := (1099327801713/2199023255552)
  nFloor := (1273804923897/9223372036854775808)
  eFloor := (930290662169/9223372036854775808)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell099
