/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1012933/8796093022208)
  b := (557113/4398046511104)
  s := [(2199023253701/2199023255552),(-739/4398046511104),(-19/2199023255552)]
  L := [(2720764148403/4722366482869645213696),(1632453652793/14167099448608935641088),(40811220301/7083549724304467820544),(1/885443715538058477568),(-1/442721857769029238784)]
  c := (1360382074201/2361183241434822606848)
  R := (-8509865242649/800000000000)
  total := (-60969343/500000000000000)
  k := 31
  n := 32
  sFloor := (34359738333/68719476736)
  nFloor := (254153972907/302231454903657293676544)
  eFloor := (742459243513/1208925819614629174706176)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell036
