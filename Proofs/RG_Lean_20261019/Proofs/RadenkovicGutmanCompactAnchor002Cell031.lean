/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1257905/17592186044416)
  b := (1383695/17592186044416)
  s := [(4398046509677/4398046511104),(-9/137438953472),(-3/1099511627776)]
  L := [(2362081784978875111669589331/10633823966279326983230456482242756608),(2517530072701/56668397794435742564352),(20979333833/9444732965739290427392),(11/3541774862152233910272),(-1/590295810358705651712)]
  c := (262243758373/1180591620717411303424)
  R := (-111138811777751/10000000000000)
  total := (-989023/12500000000000)
  k := 33
  n := 32
  sFloor := (68719476709/137438953472)
  nFloor := (391950433863/1208925819614629174706176)
  eFloor := (572501817091/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell031
