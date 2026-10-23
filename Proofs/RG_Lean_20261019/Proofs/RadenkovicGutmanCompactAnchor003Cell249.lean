/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell249
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (309211/4096)
  b := (85033/1024)
  s := [(5355920200989/4611686018427387904),(-1584425792143/4611686018427387904),(126495355419/2305843009213693952)]
  L := [(151168375718927612215771/151115727451828646838272),(-152613433/2199023255552),(533653/51539607552),(-184281/137438953472),(1655/12884901888)]
  c := (1099828439195/1099511627776)
  R := (7202420079/50000000000000)
  total := (239145769359/200000000000000)
  k := 0
  n := 32
  sFloor := (1006121279921/2305843009213693952)
  nFloor := 15833811796393618393944327743105658985490068368101979588423405948942097152080530185060171644928
  eFloor := 15828260498799402817662270548639241157509110922906686300143846896860350037817060753189090885632
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell249
