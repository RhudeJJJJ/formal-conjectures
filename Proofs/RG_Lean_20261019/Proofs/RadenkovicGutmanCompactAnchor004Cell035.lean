/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1841697/17592186044416)
  b := (1012933/8796093022208)
  s := [(2199023254145/2199023255552),(-281/2199023255552),(-7/1099511627776)]
  L := [(4745349026761990597113675131/10633823966279326983230456482242756608),(421470057731/4722366482869645213696),(31610134081/7083549724304467820544),(1/295147905179352825856),(-1/442721857769029238784)]
  c := (2107358299757/4722366482869645213696)
  R := (-215301407119311/20000000000000)
  total := (-14023821/125000000000000)
  k := 32
  n := 32
  sFloor := (1099511626925/2199023255552)
  nFloor := (231988619063/302231454903657293676544)
  eFloor := (332514293625/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell035
