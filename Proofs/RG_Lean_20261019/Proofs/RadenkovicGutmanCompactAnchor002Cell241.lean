/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell241
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1153997/32768)
  b := (317349/8192)
  s := [(3288668251495/288230376151711744),(-971266483897/288230376151711744),(77416581089/144115188075855872)]
  L := [(37838810637950269908881/37778931862957161709568),(-4139842343/13194139533312),(306648763/6597069766656),(-4926397/824633720832),(234437/412316860416)]
  c := (8601207089/8589934592)
  R := (32785776607/50000000000000)
  total := (2537680009671/1000000000000000)
  k := 0
  n := 32
  sFloor := (154514683111/36028797018963968)
  nFloor := 364778280319242450890228083414006495672428540846602475466485645949173497856
  eFloor := 364192718745398390968814208775787842734322840710903658782598052326502563840
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell241
