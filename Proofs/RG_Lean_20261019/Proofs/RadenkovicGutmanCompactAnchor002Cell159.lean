/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell159
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1907125/134217728)
  b := (524459/33554432)
  s := [(7708447166433/35184372088832),(-554948590483/35184372088832),(26892507889/17592186044416)]
  L := [(4129695587353194222159/4722366482869645213696),(377267129005/13194139533312),(-18956313677/6597069766656),(179359979/824633720832),(-5606635/412316860416)]
  c := (1923039363395/2199023255552)
  R := (-3352658771197/50000000000000)
  total := (-42252662713/500000000000000)
  k := 1
  n := 32
  sFloor := (450455224483/4398046511104)
  nFloor := (1832080795407/140737488355328)
  eFloor := (1342004577971/140737488355328)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell159
