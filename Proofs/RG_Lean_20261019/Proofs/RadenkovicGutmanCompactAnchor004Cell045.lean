/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1194217/4398046511104)
  b := (656819/2199023255552)
  s := [(4398046492179/4398046511104),(-3785/4398046511104),(-95/2199023255552)]
  L := [(1772141977811/590295810358705651712),(2126557898959/3541774862152233910272),(17721211621/590295810358705651712),(-1/221360928884514619392),(-1/36893488147419103232)]
  c := (1772141977811/590295810358705651712)
  R := (-196239453708163/20000000000000)
  total := (-265111999/1000000000000000)
  k := 29
  n := 32
  sFloor := (1099511622051/2199023255552)
  nFloor := (1560690545343/302231454903657293676544)
  eFloor := (279621429463/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell045
