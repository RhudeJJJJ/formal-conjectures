/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell196
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (253315/524288)
  b := (557293/1048576)
  s := [(1756134256341/8796093022208),(-240602173463/17592186044416),(3586476671/8796093022208)]
  L := [(4277252945356635146171/4722366482869645213696),(469040263597/13194139533312),(-7822874461/6597069766656),(-58975717/824633720832),(4798261/412316860416)]
  c := (1991751112675/2199023255552)
  R := (-4949953955457/100000000000000)
  total := (-96713406589/50000000000000)
  k := 1
  n := 32
  sFloor := (204927455785/2199023255552)
  nFloor := (1334217605099/8388608)
  eFloor := (1965519661353/16777216)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell196
