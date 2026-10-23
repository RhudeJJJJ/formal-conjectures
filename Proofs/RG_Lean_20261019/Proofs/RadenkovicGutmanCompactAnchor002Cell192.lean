/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell192
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1384143/4194304)
  b := (1522557/4194304)
  s := [(133380176365/549755813888),(-74799974735/8796093022208),(-1688826333/4398046511104)]
  L := [(1862802156746022183457/2361183241434822606848),(643837600319/26388279066624),(11748123133/13194139533312),(-375883937/1649267441664),(16138847/824633720832)]
  c := (1734869700619/2199023255552)
  R := (-5927024423959/50000000000000)
  total := (-3654353686389/1000000000000000)
  k := 1
  n := 32
  sFloor := (2055905194439/17592186044416)
  nFloor := (590607056739/536870912)
  eFloor := (228144360131/268435456)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell192
