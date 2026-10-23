/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell002
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (158597/35184372088832)
  b := (1395653/281474976710656)
  s := [(2199023255549/2199023255552),(1/4398046511104),(-1/2199023255552)]
  L := [(4000662563473/4835703278458516698824704),(2400386186669/14507109835375550096474112),(20003123643/2417851639229258349412352),(-11/906694364710971881029632),(1/151115727451828646838272)]
  c := (250041410217/302231454903657293676544)
  R := (-1391029385085801/100000000000000)
  total := (-6248353/1000000000000000)
  k := 41
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (1761652364359/1237940039285380274899124224)
  eFloor := (157813396707/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell002
