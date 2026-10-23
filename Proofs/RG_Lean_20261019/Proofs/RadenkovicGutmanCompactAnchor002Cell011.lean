/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell011
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (186981/17592186044416)
  b := (205679/17592186044416)
  s := [(137438953471/137438953472),(-5/4398046511104),(-1/2199023255552)]
  L := [(1670106547022186742389050897/340282366920938463463374607431768211456),(1780013592601/1813388729421943762059264),(2781256361/56668397794435742564352),(1/14167099448608935641088),(-1/28334198897217871282176)]
  c := (5794346069/1180591620717411303424)
  R := (-325501927197861/25000000000000)
  total := (-1723381/125000000000000)
  k := 38
  n := 32
  sFloor := (549755813883/1099511627776)
  nFloor := (277127993473/38685626227668133590597632)
  eFloor := (809573181315/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell011
