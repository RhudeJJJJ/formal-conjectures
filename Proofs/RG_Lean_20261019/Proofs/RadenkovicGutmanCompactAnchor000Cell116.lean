/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell116
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (126637/536870912)
  b := (1114405/4294967296)
  s := [(2190268620157/2199023255552),(-3480902903/4398046511104),(-84597107/2199023255552)]
  L := [(1650977483776951236597755/618970019642690137449562112),(3589093304507/6755399441055744),(88272367901/3377699720527872),(-18000707/422212465065984),(-211949/211106232532992)]
  c := (1501555274241/562949953421312)
  R := (-296334465553189/100000000000000)
  total := (-68762044667/1000000000000000)
  k := 9
  n := 32
  sFloor := (1094221785799/2199023255552)
  nFloor := (910071840283/288230376151711744)
  eFloor := (170132683203/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell116
