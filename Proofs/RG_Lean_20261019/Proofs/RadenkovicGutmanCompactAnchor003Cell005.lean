/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (844369/140737488355328)
  b := (928805/140737488355328)
  s := [(4398046511101/4398046511104)]
  L := [(2345486863871/9671406556917033397649408),(175909639777/3626777458843887524118528),(35181552937/14507109835375550096474112),(1/453347182355485940514816),(-1/906694364710971881029632)]
  c := (1172743431935/4835703278458516698824704)
  R := (-363096273404291/25000000000000)
  total := (-43423/5000000000000)
  k := 42
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1161334026711/618970019642690137449562112)
  eFloor := (555455064453/309485009821345068724781056)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell005
