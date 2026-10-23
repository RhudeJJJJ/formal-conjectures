/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell101
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (242529/4294967296)
  b := (1067127/17179869184)
  s := [(68716708545/68719476736),(-17715183/2199023255552),(-442745/1099511627776)]
  L := [(427673538982020539410679021/20282409603651670423947251286016),(1823190008423/432345564227567616),(45571401409/216172782113783808),(-100817/27021597764222976),(-1261/13510798882111488)]
  c := (759700816001/36028797018963968)
  R := (-67293152507703/12500000000000)
  total := (-3765732927/125000000000000)
  k := 16
  n := 32
  sFloor := (2198916072767/4398046511104)
  nFloor := (706473599627/4611686018427387904)
  eFloor := (674835722861/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell101
