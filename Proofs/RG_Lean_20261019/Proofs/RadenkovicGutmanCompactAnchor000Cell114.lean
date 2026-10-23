/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell114
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1674541/8589934592)
  b := (920997/4294967296)
  s := [(2193032236991/2199023255552),(-2386586575/4398046511104),(-58525033/2199023255552)]
  L := [(4516379959719823785856539/2475880078570760549798248448),(1228858379953/3377699720527872),(7595094203/422212465065984),(-2116085/105553116266496),(-25399/52776558133248)]
  c := (2053811822279/1125899906842624)
  R := (-78833005250101/25000000000000)
  total := (-302651433/5000000000000)
  k := 10
  n := 32
  sFloor := (1095890209335/2199023255552)
  nFloor := (1243184277255/576460752303423488)
  eFloor := (929624346219/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell114
