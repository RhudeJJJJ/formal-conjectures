/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (64985/536870912)
  b := (142967/1073741824)
  s := [(2196707567005/2199023255552),(-924809835/4398046511104),(-22949315/2199023255552)]
  L := [(55815751335774536147339291/79228162514264337593543950336),(3803224812893/27021597764222976),(31557556701/4503599627370496),(-5086055/1688849860263936),(-20865/281474976710656)]
  c := (1586379066105/2251799813685248)
  R := (-362901549517069/100000000000000)
  total := (-43341795273/1000000000000000)
  k := 11
  n := 32
  sFloor := (549055553193/1099511627776)
  nFloor := (239651105851/288230376151711744)
  eFloor := (1433643897921/2305843009213693952)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell109
