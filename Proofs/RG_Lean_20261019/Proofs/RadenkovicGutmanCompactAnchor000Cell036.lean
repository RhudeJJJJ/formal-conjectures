/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1012933/8796093022208)
  b := (557113/4398046511104)
  s := [(4398046506905/4398046511104),(-419/2199023255552),(-11/1099511627776)]
  L := [(424236786682271098257242449/664613997892457936451903530140172288),(226078105469/1770887431076116955136),(11303871743/1770887431076116955136),(5/885443715538058477568),(-1/221360928884514619392)]
  c := (188398979387/295147905179352825856)
  R := (-1058609024813437/100000000000000)
  total := (-237009/1953125000000)
  k := 31
  n := 32
  sFloor := (2199023253011/4398046511104)
  nFloor := (909775437051/1208925819614629174706176)
  eFloor := (1360617327859/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell036
