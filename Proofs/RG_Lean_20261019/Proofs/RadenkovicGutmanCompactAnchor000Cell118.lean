/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1225845/4294967296)
  b := (1348429/4294967296)
  s := [(2186241426287/2199023255552),(-2534058499/2199023255552),(-60778663/1099511627776)]
  L := [(603162914869177947378309/154742504910672534362390528),(218128942193/281474976710656),(15972604055/422212465065984),(-1589241/17592186044416),(-54557/26388279066624)]
  c := (2194293901517/562949953421312)
  R := (-69341630271143/25000000000000)
  total := (-15558238669/200000000000000)
  k := 9
  n := 32
  sFloor := (1091792905231/2199023255552)
  nFloor := (1332436091959/288230376151711744)
  eFloor := (31136414631/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell118
