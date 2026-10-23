/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell079
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1906817/274877906944)
  b := (1048749/137438953472)
  s := [(4398034159541/4398046511104),(-2470295/4398046511104),(-61755/2199023255552)]
  L := [(2543422950976667464028790833/1298074214633706907132624082305024),(903599435825/2305843009213693952),(67768929473/3458764513820540928),(-3243/144115188075855872),(-125/216172782113783808)]
  c := (1129506688613/576460752303423488)
  R := (-657144077922653/100000000000000)
  total := (-904997293/200000000000000)
  k := 19
  n := 32
  sFloor := (549753945717/1099511627776)
  nFloor := (497368580057/147573952589676412928)
  eFloor := (712889118819/295147905179352825856)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell079
