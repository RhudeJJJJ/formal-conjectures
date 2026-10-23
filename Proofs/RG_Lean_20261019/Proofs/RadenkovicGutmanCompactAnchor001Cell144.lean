/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell144
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (913105/268435456)
  b := (2008831/536870912)
  s := [(7749996513231/8796093022208),(-171063868073/8796093022208),(-929915255/4398046511104)]
  L := [(10002924548998859142327/151115727451828646838272),(606829069937/52776558133248),(7401943709/26388279066624),(-135588697/6597069766656),(70865/206158430208)]
  c := (582246840291/8796093022208)
  R := (-67879211127593/50000000000000)
  total := (-55951173839/125000000000000)
  k := 4
  n := 32
  sFloor := (947134101831/2199023255552)
  nFloor := (626567653601/1125899906842624)
  eFloor := (1196897671067/2251799813685248)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell144
