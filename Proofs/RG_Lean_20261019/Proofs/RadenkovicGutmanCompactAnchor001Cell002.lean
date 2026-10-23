/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell002
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (158597/35184372088832)
  b := (1395653/281474976710656)
  s := [(2199023255551/2199023255552)]
  L := [(2599048479165/19342813113834066795298816),(779710856501/29014219670751100192948224),(9746339623/7253554917687775048237056),(-7/3626777458843887524118528),(1/906694364710971881029632)]
  c := (649762119791/4835703278458516698824704)
  R := (-1481909832130747/100000000000000)
  total := (-6658003/1000000000000000)
  k := 43
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (604210662469/618970019642690137449562112)
  eFloor := (1154304847443/1237940039285380274899124224)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell002
