/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell145
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (2008831/536870912)
  b := (1104857/268435456)
  s := [(947134101831/1099511627776),(-192277172599/8796093022208),(-503758657/4398046511104)]
  L := [(23559598894917529280991/302231454903657293676544),(696580468025/52776558133248),(14108202403/52776558133248),(-84174581/3298534883328),(1950521/3298534883328)]
  c := (342837285933/4398046511104)
  R := (-63791494924913/50000000000000)
  total := (-462192955513/1000000000000000)
  k := 4
  n := 32
  sFloor := (1845947031183/4398046511104)
  nFloor := (758322087905/1125899906842624)
  eFloor := (724275374847/1125899906842624)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell145
