/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (874225/2199023255552)
  b := (1923295/4398046511104)
  s := [(2199023251161/2199023255552),(-439/1099511627776),(-11/549755813888)]
  L := [(5557131674766899419040248893/5316911983139663491615228241121378304),(740358662719/3541774862152233910272),(9254483209/885443715538058477568),(-11/442721857769029238784),(1/110680464442257309696)]
  c := (1233931107239/1180591620717411303424)
  R := (-1033953821408029/100000000000000)
  total := (-204562749/500000000000000)
  k := 30
  n := 32
  sFloor := (2199023250239/4398046511104)
  nFloor := (1147426589953/151115727451828646838272)
  eFloor := (1096041626817/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell049
