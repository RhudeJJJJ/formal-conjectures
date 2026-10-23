/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell147
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (607671/134217728)
  b := (334219/67108864)
  s := [(4470456539571/8796093022208),(-322096760393/8796093022208),(9592837407/4398046511104)]
  L := [(4117276228338943099195/9444732965739290427392),(284235230677/6597069766656),(-3741690411/2199023255552),(6648365/412316860416),(523843/137438953472)]
  c := (1917256148689/4398046511104)
  R := (-20756634822397/50000000000000)
  total := (-177388003999/1000000000000000)
  k := 2
  n := 32
  sFloor := (520943181749/2199023255552)
  nFloor := (1311592720469/1125899906842624)
  eFloor := (245250961383/281474976710656)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell147
