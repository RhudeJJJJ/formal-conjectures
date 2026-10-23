/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell134
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1408171/1073741824)
  b := (387247/268435456)
  s := [(1076419645885/1099511627776),(-35725645435/8796093022208),(-757274617/4398046511104)]
  L := [(107450871489520140157497/9671406556917033397649408),(611002867991/281474976710656),(41612494337/422212465065984),(-2074601/2199023255552),(-425723/26388279066624)]
  c := (1563615973129/140737488355328)
  R := (-112497382497341/50000000000000)
  total := (-3610993653/12500000000000)
  k := 7
  n := 32
  sFloor := (1071764621551/2199023255552)
  nFloor := (744389676929/9007199254740992)
  eFloor := (355521670625/4503599627370496)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell134
