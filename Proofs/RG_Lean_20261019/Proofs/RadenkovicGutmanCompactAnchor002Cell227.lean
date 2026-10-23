/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell227
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1215541/131072)
  b := (1337095/131072)
  s := [(1347909785231/2251799813685248),(-3098675107087/18014398509481984),(240423043783/9007199254740992)]
  L := [(4821923232338160733181/4722366482869645213696),(-17230693597/4398046511104),(3534114611/6597069766656),(-17212521/274877906944),(2244817/412316860416)]
  c := (69931873227/68719476736)
  R := (874443265913/100000000000000)
  total := (442894010543/50000000000000)
  k := 0
  n := 32
  sFloor := (2041362315581/9007199254740992)
  nFloor := 92737879183713739612375220776456310172048949248
  eFloor := 90714481840608476587412650183888371061295677440
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell227
