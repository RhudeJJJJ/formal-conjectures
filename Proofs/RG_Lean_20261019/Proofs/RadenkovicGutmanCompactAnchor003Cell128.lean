/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1589755/2147483648)
  b := (874365/1073741824)
  s := [(4367324745955/4398046511104),(-6076650001/4398046511104),(-144132485/2199023255552)]
  L := [(283488819710553439925439/77371252455336267181195264),(818742388785/1125899906842624),(59528177057/1688849860263936),(-7680263/70368744177664),(-257405/105553116266496)]
  c := (515663159077/140737488355328)
  R := (-70114973619221/25000000000000)
  total := (-204066070259/1000000000000000)
  k := 9
  n := 32
  sFloor := (545119978873/1099511627776)
  nFloor := (1029246964575/36028797018963968)
  eFloor := (984553081321/36028797018963968)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell128
