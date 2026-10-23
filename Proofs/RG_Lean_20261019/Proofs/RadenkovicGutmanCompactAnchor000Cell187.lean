/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell187
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (859445/4194304)
  b := (1890779/8388608)
  s := [(544356788197/2199023255552),(65723792251/17592186044416),(-10138192785/8796093022208)]
  L := [(112323827428566390500765/151115727451828646838272),(-56245044247/26388279066624),(12039509569/4398046511104),(-366360659/1649267441664),(2626139/274877906944)]
  c := (816593281909/1099511627776)
  R := (-7437005837631/50000000000000)
  total := (-3042246632557/1000000000000000)
  k := 1
  n := 32
  sFloor := (544356788197/4398046511104)
  nFloor := (1523290704483/68719476736)
  eFloor := (1236075661061/68719476736)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell187
