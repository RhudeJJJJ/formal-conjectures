/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1114405/4294967296)
  b := (1225845/4294967296)
  s := [(1098577701591/1099511627776),(-373066763/2199023255552),(-9268053/1099511627776)]
  L := [(70481462226428119468290329/158456325028528675187087900672),(400265125215/4503599627370496),(29907734969/6755399441055744),(-465693/281474976710656),(-17237/422212465065984)]
  c := (2003203639629/4503599627370496)
  R := (-385894227717959/100000000000000)
  total := (-772436627/7812500000000)
  k := 12
  n := 32
  sFloor := (2196763800313/4398046511104)
  nFloor := (466130328625/144115188075855872)
  eFloor := (445255455231/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell117
