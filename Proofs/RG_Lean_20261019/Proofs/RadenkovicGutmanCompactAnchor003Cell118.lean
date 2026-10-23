/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1225845/4294967296)
  b := (1348429/4294967296)
  s := [(2196718079097/2199023255552),(-920540297/4398046511104),(-22835389/2199023255552)]
  L := [(21717017987171300661912465/39614081257132168796771975168),(2959312168141/27021597764222976),(73642709465/13510798882111488),(-4235833/1688849860263936),(-52097/844424930131968)]
  c := (308617387463/562949953421312)
  R := (-75088437291063/20000000000000)
  total := (-52888122173/500000000000000)
  k := 11
  n := 32
  sFloor := (2196234973559/4398046511104)
  nFloor := (611938351793/144115188075855872)
  eFloor := (1170736373247/288230376151711744)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell118
