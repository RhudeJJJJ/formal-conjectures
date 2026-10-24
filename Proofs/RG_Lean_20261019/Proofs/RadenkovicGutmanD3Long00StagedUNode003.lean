/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e003 : NestedArithmetic.Expr 3 := .pow e000 2
noncomputable def p003 : NestedHorner.Poly 3 := [[],[[]],[[1]]]
theorem step003 : p003=NestedArithmetic.power p000 2 := by decide +kernel
#print axioms step003
theorem h003 : NestedArithmetic.compile e003=p003 := by
  change NestedArithmetic.power (NestedArithmetic.compile e000) 2=p003
  rw [h000]
  exact step003.symm
#print axioms h003
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
