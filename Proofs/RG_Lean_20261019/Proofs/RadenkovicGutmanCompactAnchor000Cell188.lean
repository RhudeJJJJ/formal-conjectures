/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell188
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1890779/8388608)
  b := (129991/524288)
  s := [(4400301712257/17592186044416),(27602344921/17592186044416),(-9796032705/8796093022208)]
  L := [(14047910381489783120443/18889465931478580854784),(78817700789/26388279066624),(33974133577/13194139533312),(-402918119/1649267441664),(10442915/824633720832)]
  c := (1635392008057/2199023255552)
  R := (-370163438923/2500000000000)
  total := (-3302681198461/1000000000000000)
  k := 1
  n := 32
  sFloor := (34377357127/274877906944)
  nFloor := (1319023349603/34359738368)
  eFloor := (1063880649445/34359738368)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell188
