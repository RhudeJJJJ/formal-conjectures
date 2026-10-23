/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell187
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (859445/4194304)
  b := (1890779/8388608)
  s := [(5142290349981/17592186044416),(-54993854547/8796093022208),(-1116138771/4398046511104)]
  L := [(6253322981005548792877/9444732965739290427392),(118789861231/6597069766656),(80708575/206158430208),(-54663305/824633720832),(1046447/206158430208)]
  c := (1455965214643/2199023255552)
  R := (-20617211429101/100000000000000)
  total := (-4084810022281/1000000000000000)
  k := 1
  n := 32
  sFloor := (628479760725/4398046511104)
  nFloor := (1384274903567/34359738368)
  eFloor := (572468939841/17179869184)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell187
