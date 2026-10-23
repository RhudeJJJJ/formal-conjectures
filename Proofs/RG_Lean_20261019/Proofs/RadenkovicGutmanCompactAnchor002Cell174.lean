/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell174
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (995809/16777216)
  b := (1095389/16777216)
  s := [(5498142733011/35184372088832),(196928538225/35184372088832),(4665170699/17592186044416)]
  L := [(9049100691734394600409/9444732965739290427392),(-75913636725/4398046511104),(-1196566409/2199023255552),(36273369/274877906944),(-1302463/137438953472)]
  c := (2068023901317/2199023255552)
  R := (-3070988637651/100000000000000)
  total := (-9647511047/62500000000000)
  k := 1
  n := 32
  sFloor := (343633920813/4398046511104)
  nFloor := (650006625647/2199023255552)
  eFloor := (990100518281/4398046511104)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell174
