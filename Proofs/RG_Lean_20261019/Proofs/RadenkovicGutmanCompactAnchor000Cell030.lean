/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell030
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (571775/8796093022208)
  b := (1257905/17592186044416)
  s := [(2199023254883/2199023255552),(-267/4398046511104),(-7/2199023255552)]
  L := [(540701035353925500449486447/2658455991569831745807614120560689152),(96047798193/2361183241434822606848),(28814339407/14167099448608935641088),(1/590295810358705651712),(-1/885443715538058477568)]
  c := (1920955964443/9444732965739290427392)
  R := (-1115795005233527/100000000000000)
  total := (-18053923/250000000000000)
  k := 33
  n := 32
  sFloor := (1099511627371/2199023255552)
  nFloor := (36235403779/151115727451828646838272)
  eFloor := (867071433337/4835703278458516698824704)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell030
