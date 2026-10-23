/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell233
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (269175/16384)
  b := (592185/32768)
  s := [(4001926026253/36028797018963968),(-586537602599/18014398509481984),(46407092113/9007199254740992)]
  L := [(19023332476978522277695/18889465931478580854784),(-6050645719/4398046511104),(1313125631/6597069766656),(-6846505/274877906944),(954025/412316860416)]
  c := (34562032411/34359738368)
  R := (58702677437/20000000000000)
  total := (33057015033/6250000000000)
  k := 0
  n := 32
  sFloor := (1507239594753/36028797018963968)
  nFloor := 14510366907799548635614529074179963613065261452509210868711424
  eFloor := 14405057472977827673647803344270063545233353635008776733982720
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell233
