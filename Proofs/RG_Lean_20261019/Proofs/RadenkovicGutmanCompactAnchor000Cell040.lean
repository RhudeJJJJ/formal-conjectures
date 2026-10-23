/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell040
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1483033/8796093022208)
  b := (203917/1099511627776)
  s := [(549755812763/549755813888),(-901/2199023255552),(-11/549755813888)]
  L := [(113673315394585028788845843/83076749736557242056487941267521536),(1938470038765/7083549724304467820544),(48461652443/3541774862152233910272),(7/221360928884514619392),(-5/221360928884514619392)]
  c := (1615394970067/1180591620717411303424)
  R := (-1020485101649241/100000000000000)
  total := (-171238667/1000000000000000)
  k := 30
  n := 32
  sFloor := (2199023250107/4398046511104)
  nFloor := (487544661641/302231454903657293676544)
  eFloor := (364574425577/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell040
