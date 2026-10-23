/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell242
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (317349/8192)
  b := (1396335/32768)
  s := [(154514683111/18014398509481984),(-1460823426407/576460752303423488),(116479680347/288230376151711744)]
  L := [(75657017661294807018389/75557863725914323419136),(-1143897765/4398046511104),(254544943/6597069766656),(-1365153/274877906944),(195149/412316860416)]
  c := (1100706016939/1099511627776)
  R := (13571262861/25000000000000)
  total := (3697983299/1600000000000)
  k := 0
  n := 32
  sFloor := (1858302896919/576460752303423488)
  nFloor := 23392991755821993484105732835816332385451517746519387445738782305745371136
  eFloor := 23361932793796364210944762103077220505347222555378091311522104459306991616
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell242
