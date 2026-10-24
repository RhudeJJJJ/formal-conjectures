/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e144 : NestedArithmetic.Expr 3 := .pow e000 10
noncomputable def p144 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[1]]]
theorem step144 : p144=NestedArithmetic.power p000 10 := by decide +kernel
#print axioms step144
theorem h144 : NestedArithmetic.compile e144=p144 := by
  change NestedArithmetic.power (NestedArithmetic.compile e000) 10=p144
  rw [h000]
  exact step144.symm
#print axioms h144
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
