/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell162
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1269189/67108864)
  b := (1396107/67108864)
  s := [(1653762353881/4398046511104),(-182606448495/8796093022208),(9087947053/4398046511104)]
  L := [(8994422964212718759655/18889465931478580854784),(25733642027/1099511627776),(-14567425853/6597069766656),(38158955/274877906944),(-2536813/412316860416)]
  c := (523544322013/1099511627776)
  R := (-3709998469717/10000000000000)
  total := (-680123962271/1000000000000000)
  k := 2
  n := 32
  sFloor := (785773538343/4398046511104)
  nFloor := (625389700649/35184372088832)
  eFloor := (1191162376835/70368744177664)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell162
