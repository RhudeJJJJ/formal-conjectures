/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell174
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (995809/16777216)
  b := (1095389/16777216)
  s := [(2568302053529/8796093022208),(55286025359/17592186044416),(1788082261/8796093022208)]
  L := [(347664624356802415299/590295810358705651712),(-17121859235/13194139533312),(-2321398645/6597069766656),(92001659/824633720832),(-4370567/412316860416)]
  c := (1291746237547/2199023255552)
  R := (-26600915576361/100000000000000)
  total := (-1574799215673/1000000000000000)
  k := 1
  n := 32
  sFloor := (321037756691/2199023255552)
  nFloor := (1019819432757/4398046511104)
  eFloor := (474449712071/2199023255552)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell174
