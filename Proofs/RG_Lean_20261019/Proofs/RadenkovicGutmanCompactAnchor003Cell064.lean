/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell064
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (912959/549755813888)
  b := (502127/274877906944)
  s := [(4398046354763/4398046511104),(-7817/1099511627776),(-391/1099511627776)]
  L := [(192952662881674222410441015/10384593717069655257060992658440192),(3290394145601/885443715538058477568),(82259029843/442721857769029238784),(-143/55340232221128654848),(-7/27670116110564327424)]
  c := (1371011129561/73786976294838206464)
  R := (-178011442826389/20000000000000)
  total := (-735015899/500000000000000)
  k := 26
  n := 32
  sFloor := (2199023160965/4398046511104)
  nFloor := (339418216913/2361183241434822606848)
  eFloor := (649362072275/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell064
