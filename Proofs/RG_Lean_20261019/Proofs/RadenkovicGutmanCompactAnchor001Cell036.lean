/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1012933/8796093022208)
  b := (557113/4398046511104)
  s := [(4398046510367/4398046511104),(-149/4398046511104),(-3/2199023255552)]
  L := [(1656555193737/18889465931478580854784),(662620114891/37778931862957161709568),(49696361377/56668397794435742564352),(1/2361183241434822606848),(-1/3541774862152233910272)]
  c := (1656555193737/18889465931478580854784)
  R := (-1157856499190679/100000000000000)
  total := (-13277763/100000000000000)
  k := 34
  n := 32
  sFloor := (1099511627553/2199023255552)
  nFloor := (770211344061/1208925819614629174706176)
  eFloor := (367859565889/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell036
