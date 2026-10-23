/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell224
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (913255/131072)
  b := (2009161/262144)
  s := [(6143682801581/4503599627370496),(-1728047507535/4503599627370496),(131283252405/2251799813685248)]
  L := [(4889901896958920726251/4722366482869645213696),(-83110538405/13194139533312),(5337544771/6597069766656),(-71884759/824633720832),(2864165/412316860416)]
  c := (1132394510095/1099511627776)
  R := (1473415987413/100000000000000)
  total := (2233541159221/200000000000000)
  k := 0
  n := 32
  sFloor := (584775224857/1125899906842624)
  nFloor := 3026280972485712552313352388984128405504
  eFloor := 2914633033640473273450476803022510882816
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell224
