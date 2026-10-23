/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell114
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1674541/8589934592)
  b := (920997/4294967296)
  s := [(4395936547561/4398046511104),(-210834799/2199023255552),(-1313033/274877906944)]
  L := [(318410144502882971070773587/1267650600228229401496703205376),(2713479668209/54043195528445952),(22564523451/9007199254740992),(-1785001/3377699720527872),(-7379/562949953421312)]
  c := (282805018961/1125899906842624)
  R := (-207233387744977/50000000000000)
  total := (-15970689373/200000000000000)
  k := 12
  n := 32
  sFloor := (2197746934717/4398046511104)
  nFloor := (263118645595/144115188075855872)
  eFloor := (1005341507263/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell114
