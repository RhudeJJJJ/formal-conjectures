/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (150567/8796093022208)
  b := (1324989/70368744177664)
  s := [(4398046511087/4398046511104),(-1/1099511627776)]
  L := [(2386591102917/1208925819614629174706176),(2863895057849/7253554917687775048237056),(71597019839/3626777458843887524118528),(-5/453347182355485940514816),(1/226673591177742970257408)]
  c := (596647775729/302231454903657293676544)
  R := (-673772182446331/50000000000000)
  total := (-22983599/1000000000000000)
  k := 39
  n := 32
  sFloor := (2199023255541/4398046511104)
  nFloor := (590843099223/38685626227668133590597632)
  eFloor := (1130378630823/77371252455336267181195264)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell016
