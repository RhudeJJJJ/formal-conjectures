/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1457487/70368744177664)
  b := (1603235/70368744177664)
  s := [(4398046511079/4398046511104),(-3/4398046511104),(-1/2199023255552)]
  L := [(6988401107673/2417851639229258349412352),(4193020526285/7253554917687775048237056),(34941669915/1208925819614629174706176),(-11/453347182355485940514816),(1/75557863725914323419136)]
  c := (873550138459/302231454903657293676544)
  R := (-1328482435965369/100000000000000)
  total := (-27415319/1000000000000000)
  k := 39
  n := 32
  sFloor := (2199023255537/4398046511104)
  nFloor := (865051529781/38685626227668133590597632)
  eFloor := (827491905305/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell018
