/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell004
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (767609/140737488355328)
  b := (844369/140737488355328)
  s := [(2199023255551/2199023255552),(1/4398046511104),(-1/2199023255552)]
  L := [(3805262119343/19342813113834066795298816),(2283130502219/58028439341502200385896448),(57077593355/29014219670751100192948224),(-5/3626777458843887524118528),(1/1813388729421943762059264)]
  c := (1902631059671/9671406556917033397649408)
  R := (-731423929350849/50000000000000)
  total := (-1988039/250000000000000)
  k := 43
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (884623724577/618970019642690137449562112)
  eFloor := (211251951693/154742504910672534362390528)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell004
