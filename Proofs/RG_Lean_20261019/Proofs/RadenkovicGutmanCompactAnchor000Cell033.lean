/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (95129/1099511627776)
  b := (837135/8796093022208)
  s := [(2199023254367/2199023255552),(-237/2199023255552),(-3/549755813888)]
  L := [(1915767090132321919981156163/5316911983139663491615228241121378304),(4083692433641/56668397794435742564352),(102092042273/28334198897217871282176),(13/3541774862152233910272),(-5/1770887431076116955136)]
  c := (1701542986627/4722366482869645213696)
  R := (-1087202020289419/100000000000000)
  total := (-93644929/1000000000000000)
  k := 32
  n := 32
  sFloor := (1099511627059/2199023255552)
  nFloor := (128386279173/302231454903657293676544)
  eFloor := (1536067816193/4835703278458516698824704)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell033
