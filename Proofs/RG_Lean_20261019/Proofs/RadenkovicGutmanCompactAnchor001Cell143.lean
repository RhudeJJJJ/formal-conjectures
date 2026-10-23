/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell143
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (51881/16777216)
  b := (913105/268435456)
  s := [(3951537620561/4398046511104),(-150662248957/8796093022208),(-1208239467/4398046511104)]
  L := [(33842964086458235464121/604462909807314587353088),(4197678826445/422212465065984),(58938383885/211106232532992),(-426211163/26388279066624),(2337079/13194139533312)]
  c := (1969919777851/35184372088832)
  R := (-28826091892513/20000000000000)
  total := (-17300065137/40000000000000)
  k := 5
  n := 32
  sFloor := (1937499128307/4398046511104)
  nFloor := (1035452578723/2251799813685248)
  eFloor := (989001029303/2251799813685248)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell143
