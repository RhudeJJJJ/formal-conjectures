/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (164231/268435456)
  b := (90327/134217728)
  s := [(4377404240011/4398046511104),(-4097801173/4398046511104),(-98903275/2199023255552)]
  L := [(1524252491984006016898609/618970019642690137449562112),(1654971207505/3377699720527872),(40521555091/1688849860263936),(-10525771/211106232532992),(-122143/105553116266496)]
  c := (1386299565623/562949953421312)
  R := (-300327635864107/100000000000000)
  total := (-22599569957/125000000000000)
  k := 9
  n := 32
  sFloor := (136659644759/274877906944)
  nFloor := (647924186229/36028797018963968)
  eFloor := (1237812693595/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell126
