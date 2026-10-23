/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell177
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1325419/16777216)
  b := (182245/2097152)
  s := [(5337961686047/17592186044416),(38909551675/8796093022208),(-1375842677/4398046511104)]
  L := [(1378265574029523569839/2361183241434822606848),(-5593579807/3298534883328),(2478073439/6597069766656),(39374593/824633720832),(-3149477/412316860416)]
  c := (80049688493/137438953472)
  R := (-2702661478709/10000000000000)
  total := (-2131270723551/1000000000000000)
  k := 1
  n := 32
  sFloor := (1334490421511/8796093022208)
  nFloor := (1125525158589/2199023255552)
  eFloor := (128807448055/274877906944)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell177
