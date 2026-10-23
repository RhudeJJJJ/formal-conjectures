/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (656819/2199023255552)
  b := (1445001/4398046511104)
  s := [(2199023253073/2199023255552),(-991/4398046511104),(-25/2199023255552)]
  L := [(5572189419723/9444732965739290427392),(1114431095685/9444732965739290427392),(83581822763/14167099448608935641088),(-3/590295810358705651712),(1/885443715538058477568)]
  c := (696523677465/1180591620717411303424)
  R := (-212509350146831/20000000000000)
  total := (-157960419/500000000000000)
  k := 31
  n := 32
  sFloor := (274877906569/549755813888)
  nFloor := (10120218911/2361183241434822606848)
  eFloor := (1237376931909/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell046
