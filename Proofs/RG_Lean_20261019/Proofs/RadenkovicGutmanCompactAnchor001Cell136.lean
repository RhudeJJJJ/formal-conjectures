/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell136
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (851943/536870912)
  b := (937137/536870912)
  s := [(2132435002883/2199023255552),(-25368593017/4398046511104),(-496410057/2199023255552)]
  L := [(19456753618342471682923/1208925819614629174706176),(1313763756001/422212465065984),(28497795377/211106232532992),(-50068183/26388279066624),(-343001/13194139533312)]
  c := (1132532117093/70368744177664)
  R := (-516161656549/250000000000)
  total := (-320221598003/1000000000000000)
  k := 6
  n := 32
  sFloor := (2119254296317/4398046511104)
  nFloor := (1089942537985/9007199254740992)
  eFloor := (1041109384697/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell136
