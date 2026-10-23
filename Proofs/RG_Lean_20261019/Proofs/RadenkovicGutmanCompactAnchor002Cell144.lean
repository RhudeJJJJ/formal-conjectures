/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell144
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (913105/268435456)
  b := (2008831/536870912)
  s := [(703054853105/1099511627776),(-327276061393/8796093022208),(6572610677/4398046511104)]
  L := [(5687656881912923072145/18889465931478580854784),(666698381425/17592186044416),(-5925720049/8796093022208),(-55100247/1099511627776),(3000229/549755813888)]
  c := (662130406349/2199023255552)
  R := (-60015302051571/100000000000000)
  total := (-193988468261/1000000000000000)
  k := 2
  n := 32
  sFloor := (165947124525/549755813888)
  nFloor := (12920271077/17592186044416)
  eFloor := (1208015303133/2251799813685248)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell144
