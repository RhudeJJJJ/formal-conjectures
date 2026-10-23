/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell040
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1483033/8796093022208)
  b := (203917/1099511627776)
  s := [(1099511627373/1099511627776),(-161/2199023255552),(-1/274877906944)]
  L := [(452220339139/2361183241434822606848),(361775539337/9444732965739290427392),(27133110505/14167099448608935641088),(1/590295810358705651712),(-1/885443715538058477568)]
  c := (452220339139/2361183241434822606848)
  R := (-1118800722289203/100000000000000)
  total := (-93907389/500000000000000)
  k := 33
  n := 32
  sFloor := (2199023254577/4398046511104)
  nFloor := (895641541575/604462909807314587353088)
  eFloor := (428376865535/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell040
