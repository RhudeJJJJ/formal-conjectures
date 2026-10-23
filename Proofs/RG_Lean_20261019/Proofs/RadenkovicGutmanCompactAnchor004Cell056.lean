/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (851807/1099511627776)
  b := (936987/1099511627776)
  s := [(4398046357051/4398046511104),(-15405/2199023255552),(-385/1099511627776)]
  L := [(3606404213801/147573952589676412928),(1081912334309/221360928884514619392),(27047582197/110680464442257309696),(-47/13835058055282163712),(-1/6917529027641081856)]
  c := (450800526725/18446744073709551616)
  R := (-438178219207559/50000000000000)
  total := (-675169943/1000000000000000)
  k := 26
  n := 32
  sFloor := (1099511581175/2199023255552)
  nFloor := (1588044639469/37778931862957161709568)
  eFloor := (1138089324547/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell056
