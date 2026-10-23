/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1603499/34359738368)
  b := (220481/4294967296)
  s := [(4397925502861/4398046511104),(-24200459/4398046511104),(-604885/2199023255552)]
  L := [(73027854405629300165573635/5070602400912917605986812821504),(1245301249051/432345564227567616),(10376197655/72057594037927936),(-23513/13510798882111488),(-197/4503599627370496)]
  c := (1037788229121/72057594037927936)
  R := (-111481292496871/20000000000000)
  total := (-5157397171/200000000000000)
  k := 17
  n := 32
  sFloor := (549737511579/1099511627776)
  nFloor := (241265909167/2305843009213693952)
  eFloor := (230461344503/2305843009213693952)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell099
