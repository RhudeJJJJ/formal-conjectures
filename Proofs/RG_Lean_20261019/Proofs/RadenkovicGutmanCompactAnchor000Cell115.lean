/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (920997/4294967296)
  b := (126637/536870912)
  s := [(4383560837341/4398046511104),(-2882784217/4398046511104),(-70406405/2199023255552)]
  L := [(1365407488653311575403797/618970019642690137449562112),(2970369691741/6755399441055744),(24420891899/1125899906842624),(-12348157/422212465065984),(-48979/70368744177664)]
  c := (1241830876691/562949953421312)
  R := (-152915098185139/50000000000000)
  total := (-64546328799/1000000000000000)
  k := 9
  n := 32
  sFloor := (2190268620157/4398046511104)
  nFloor := (752126013763/288230376151711744)
  eFloor := (1124844850949/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell115
