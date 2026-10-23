/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell157
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1576137/134217728)
  b := (866875/67108864)
  s := [(578606779379/2199023255552),(-44402552625/2199023255552),(7985345313/4398046511104)]
  L := [(958547036602729894501/1180591620717411303424),(153718988599/4398046511104),(-20258250713/6597069766656),(57902455/274877906944),(-4856707/412316860416)]
  c := (1785432988037/2199023255552)
  R := (-1041761654421/10000000000000)
  total := (-13819650757/125000000000000)
  k := 1
  n := 32
  sFloor := (1076393798821/8796093022208)
  nFloor := (1377249660685/140737488355328)
  eFloor := (1979161284109/281474976710656)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell157
