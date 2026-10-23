/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (904987/70368744177664)
  b := (995485/70368744177664)
  s := [(2199023255547/2199023255552),(-1/2199023255552)]
  L := [(1322297423421/1208925819614629174706176),(3173489269351/14507109835375550096474112),(79336618033/7253554917687775048237056),(5/906694364710971881029632),(-1/453347182355485940514816)]
  c := (1322297423421/1208925819614629174706176)
  R := (-688534565821173/50000000000000)
  total := (-44119/2500000000000)
  k := 40
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (614798999397/77371252455336267181195264)
  eFloor := (1174533170777/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell013
