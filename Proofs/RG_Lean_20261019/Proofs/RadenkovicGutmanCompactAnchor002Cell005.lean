/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (844369/140737488355328)
  b := (928805/140737488355328)
  s := [(4398046511093/4398046511104),(-1/2199023255552)]
  L := [(532149684435527637695090313/340282366920938463463374607431768211456),(283583296757/906694364710971881029632),(28358027389/1813388729421943762059264),(1/56668397794435742564352),(-1/113336795588871485128704)]
  c := (1890575463063/1208925819614629174706176)
  R := (-1359193603416419/100000000000000)
  total := (-4062747/500000000000000)
  k := 40
  n := 32
  sFloor := (2199023255545/4398046511104)
  nFloor := (176603791581/77371252455336267181195264)
  eFloor := (257956064977/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell005
