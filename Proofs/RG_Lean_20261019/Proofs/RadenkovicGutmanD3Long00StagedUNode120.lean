/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e120 : NestedArithmetic.Expr 3 := .pow e000 0
noncomputable def p120 : NestedHorner.Poly 3 := [[[1]]]
theorem step120 : p120=NestedArithmetic.power p000 0 := by decide +kernel
#print axioms step120
theorem h120 : NestedArithmetic.compile e120=p120 := by
  change NestedArithmetic.power (NestedArithmetic.compile e000) 0=p120
  rw [h000]
  exact step120.symm
#print axioms h120
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
