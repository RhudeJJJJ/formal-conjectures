/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1114405/4294967296)
  b := (1225845/4294967296)
  s := [(2197117596225/2199023255552),(-95152127/549755813888),(-4727155/549755813888)]
  L := [(574449335367334885996556179/1267650600228229401496703205376),(305836079597/3377699720527872),(5077890875/1125899906842624),(-362075/211106232532992),(-2977/70368744177664)]
  c := (2040854011537/4503599627370496)
  R := (-192481597995713/50000000000000)
  total := (-9863033873/100000000000000)
  k := 12
  n := 32
  sFloor := (2196718079097/4398046511104)
  nFloor := (252866894291/72057594037927936)
  eFloor := (967550110789/288230376151711744)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell117
