/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell220
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (311883/65536)
  b := (1372285/262144)
  s := [(2216503324313/562949953421312),(-1184343258955/1125899906842624),(85536227343/562949953421312)]
  L := [(20165469988527631173883/18889465931478580854784),(-47047941279/4398046511104),(2542262185/2199023255552),(-26198869/274877906944),(708775/137438953472)]
  c := (1163194859749/1099511627776)
  R := (1407607556443/50000000000000)
  total := (2887840249673/200000000000000)
  k := 0
  n := 32
  sFloor := (854933961089/562949953421312)
  nFloor := 4810627010045520602652772180951040
  eFloor := 4470880915203707497967732729577472
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell220
