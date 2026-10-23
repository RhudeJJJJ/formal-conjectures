/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell135
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (387247/268435456)
  b := (851943/536870912)
  s := [(8574116972411/8796093022208),(-42633279013/8796093022208),(-871840933/4398046511104)]
  L := [(64694343112629213228309/4835703278458516698824704),(1098352810381/422212465065984),(24427822765/211106232532992),(-35407975/26388279066624),(-275173/13194139533312)]
  c := (1882853193459/140737488355328)
  R := (-107852702198199/50000000000000)
  total := (-30439975389/100000000000000)
  k := 7
  n := 32
  sFloor := (2132435002883/4398046511104)
  nFloor := (900742347277/9007199254740992)
  eFloor := (860389234403/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell135
