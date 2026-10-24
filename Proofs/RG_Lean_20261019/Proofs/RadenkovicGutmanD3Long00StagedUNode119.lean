/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode006
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e119 : NestedArithmetic.Expr 3 := .pow e006 4
noncomputable def p119 : NestedHorner.Poly 3 := [[[1]]]
theorem step119 : p119=NestedArithmetic.power p006 4 := by decide +kernel
#print axioms step119
theorem h119 : NestedArithmetic.compile e119=p119 := by
  change NestedArithmetic.power (NestedArithmetic.compile e006) 4=p119
  rw [h006]
  exact step119.symm
#print axioms h119
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
