/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell170
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (85019/2097152)
  b := (748167/16777216)
  s := [(318660661635/1099511627776),(-44531615421/17592186044416),(8040031681/8796093022208)]
  L := [(2758109808183152080399/4722366482869645213696),(125087544961/26388279066624),(-5854966619/4398046511104),(268283693/1649267441664),(-3257505/274877906944)]
  c := (642172481907/1099511627776)
  R := (-26888222721923/100000000000000)
  total := (-1083247190297/1000000000000000)
  k := 1
  n := 32
  sFloor := (1267529758525/8796093022208)
  nFloor := (808273975271/8796093022208)
  eFloor := (190496014445/2199023255552)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell170
