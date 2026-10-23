/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (920997/4294967296)
  b := (126637/536870912)
  s := [(4386291825627/4398046511104),(-2341453327/4398046511104),(-57435951/2199023255552)]
  L := [(4622932382596615252833783/2475880078570760549798248448),(2515797701251/6755399441055744),(62206546561/3377699720527872),(-8541679/422212465065984),(-102601/211106232532992)]
  c := (2102266254313/1125899906842624)
  R := (-157083049512571/50000000000000)
  total := (-33166574933/500000000000000)
  k := 10
  n := 32
  sFloor := (2191917750199/4398046511104)
  nFloor := (7252014571/2251799813685248)
  eFloor := (166311648705/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell115
