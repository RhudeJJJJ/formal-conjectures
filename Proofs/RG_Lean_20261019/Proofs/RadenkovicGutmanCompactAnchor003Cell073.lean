/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell073
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (538175/137438953472)
  b := (1183985/274877906944)
  s := [(1099511410467/1099511627776),(-173845/4398046511104),(-4347/2199023255552)]
  L := [(1072791126110463878788993227/10384593717069655257060992658440192),(4573582659583/221360928884514619392),(114339467407/110680464442257309696),(-1225/13835058055282163712),(-19/6917529027641081856)]
  c := (952829927057/9223372036854775808)
  R := (-160855701111927/20000000000000)
  total := (-782597421/250000000000000)
  k := 24
  n := 32
  sFloor := (34359730151/68719476736)
  nFloor := (471780112905/590295810358705651712)
  eFloor := (451295918239/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell073
