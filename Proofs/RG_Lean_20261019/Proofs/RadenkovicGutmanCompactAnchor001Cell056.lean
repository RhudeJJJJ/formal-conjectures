/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (851807/1099511627776)
  b := (936987/1099511627776)
  s := [(4398046477755/4398046511104),(-6669/4398046511104),(-167/2199023255552)]
  L := [(659472459740966244692095033/166153499473114484112975882535043072),(702869266595/885443715538058477568),(17571586691/442721857769029238784),(-11/55340232221128654848),(1/27670116110564327424)]
  c := (73216150891/18446744073709551616)
  R := (-15113076313807/1562500000000)
  total := (-372787857/500000000000000)
  k := 28
  n := 32
  sFloor := (137438952211/274877906944)
  nFloor := (1089333540551/37778931862957161709568)
  eFloor := (1040550146199/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell056
