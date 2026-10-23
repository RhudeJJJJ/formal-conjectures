/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1483271/4294967296)
  b := (815799/2147483648)
  s := [(4365137847957/4398046511104),(-6507731941/4398046511104),(-77094133/1099511627776)]
  L := [(795685447880191873232683/154742504910672534362390528),(3447067250953/3377699720527872),(27848771679/562949953421312),(-32267791/211106232532992),(-119811/35184372088832)]
  c := (1447343398249/281474976710656)
  R := (-52703138140747/20000000000000)
  total := (-89347239619/1000000000000000)
  k := 8
  n := 32
  sFloor := (1089580434871/2199023255552)
  nFloor := (272490115975/36028797018963968)
  eFloor := (1592051967817/288230376151711744)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell120
