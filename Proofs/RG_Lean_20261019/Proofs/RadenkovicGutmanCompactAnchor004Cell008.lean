/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (561927/70368744177664)
  b := (1236239/140737488355328)
  s := [(4398046511087/4398046511104),(-5/4398046511104),(1/2199023255552)]
  L := [(784732812267/302231454903657293676544),(470838011557/906694364710971881029632),(23541816769/906694364710971881029632),(1/28334198897217871282176),(-1/56668397794435742564352)]
  c := (784732812267/302231454903657293676544)
  R := (-1333843547671181/100000000000000)
  total := (-5306333/500000000000000)
  k := 39
  n := 32
  sFloor := (1099511627771/2199023255552)
  nFloor := (1382197465735/309485009821345068724781056)
  eFloor := (1981133453121/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell008
